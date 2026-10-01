use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    proto::{
        FIGHT_GAME_SEND, IL2CPP_OBJECT_NEW_RVA, MessageMinimalInfo, NETWORK_MANAGER_SEND_NAME,
        NETWORK_MANAGER_SEND_VA, XLUA_OBJECT_TRANSLATOR_DELEGATE,
        XLUA_OBJECT_TRANSLATOR_METHOD_CLASS, XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS,
        XLUA_REGISTER_OBJECT_RVA,
    },
    script::TYPE_INFOS,
};
use iced_x86::{Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};
use il2cpp::vm::method::Il2CppMethod;
use il2cpp::{
    FUNCTIONS_TABLE_REFLECTION, GA_BASE,
    api::Il2CppClass,
    get_cached_class, get_native_method,
    vm::{
        metadata_cache, native_collections::Dictionary, object::Il2CppObject, r#type::Il2CppType,
    },
};
use reflection::{field_info::FieldInfo, runtime_type::RuntimeType};
use std::borrow::Cow;
use utils::game_assembly_slice;

const RSP_NOTIFY_DICT_TYPE: &str = "Dictionary<RuntimeTypeHandle, ushort>";
/// How many typedefs after `NotifyType` are searched for the CmdId dictionary holder.
const RSP_NOTIFY_SEARCH_WINDOW: u32 = 8;

fn find_rsp_notify_dict_field(runtime_type: RuntimeType) -> Option<FieldInfo> {
    runtime_type.get_fields(62).into_iter().find(|v| {
        v.get_field_type()
            .is_ok_and(|ty| ty.format_type_name(true) == RSP_NOTIFY_DICT_TYPE)
    })
}

fn read_rsp_notify_dict(
    holder: RuntimeType,
    field: FieldInfo,
) -> Option<HashMap<RuntimeType, u16>> {
    let holder_name = holder.il_name();
    let Ok(dictionary) = field.get_value(Il2CppObject::NULL) else {
        log::error!("[Proto Dumper] failed to read CmdId dictionary from {holder_name}");
        return None;
    };
    if dictionary.0 == 0 {
        log::error!(
            "[Proto Dumper] CmdId dictionary on {holder_name} is null (static constructor not run yet? try again after logging in)"
        );
        return None;
    }

    let dict = unsafe { *(dictionary.0 as *const Dictionary<Il2CppType, u16>) };
    let map = dict
        .iter()
        .filter_map(|(ty, cmdid)| RuntimeType::from_il2cpp_type(ty).ok().map(|rt| (rt, cmdid)))
        .collect::<HashMap<_, _>>();
    log::debug!(
        "[Proto Dumper] rsp/notify CmdIds: {} entries from {holder_name}",
        map.len()
    );
    Some(map)
}

pub fn get_rsp_notify_map() -> HashMap<RuntimeType, u16> {
    let (start, end) = unsafe { (il2cpp::ASSEMBLY_CSHARP_START, il2cpp::MAX_TYPEDEFINDEX) };
    let type_at = |index: u32| {
        RuntimeType::from_class(metadata_cache::get_typeinfo_from_typedefindex(index)).ok()
    };

    let notify_type_index = (start..end).find(|&index| {
        type_at(index)
            .and_then(|rt| rt.get_name().ok())
            .is_some_and(|name| name.as_str() == "NotifyType")
    });

    // Fast path: the holder class sits right after `NotifyType`.
    if let Some(notify_index) = notify_type_index {
        let window_end = notify_index
            .saturating_add(RSP_NOTIFY_SEARCH_WINDOW + 1)
            .min(end);
        for index in notify_index + 1..window_end {
            if let Some(rt) = type_at(index)
                && let Some(field) = find_rsp_notify_dict_field(rt)
            {
                if index != notify_index + 2 {
                    log::warn!(
                        "[Proto Dumper] CmdId dictionary found at NotifyType+{}, expected +2",
                        index - notify_index
                    );
                }
                if let Some(map) = read_rsp_notify_dict(rt, field) {
                    return map;
                }
            }
        }
        log::warn!(
            "[Proto Dumper] no `{RSP_NOTIFY_DICT_TYPE}` field within {RSP_NOTIFY_SEARCH_WINDOW} types after NotifyType (#{notify_index}), scanning Assembly-CSharp"
        );
    } else {
        log::warn!(
            "[Proto Dumper] NotifyType not found, scanning Assembly-CSharp for CmdId dictionary"
        );
    }

    // Slow path: any static `Dictionary<RuntimeTypeHandle, ushort>` in Assembly-CSharp.
    for index in start..end {
        if let Some(rt) = type_at(index)
            && let Some(field) = find_rsp_notify_dict_field(rt)
            && let Some(map) = read_rsp_notify_dict(rt, field)
        {
            return map;
        }
    }

    log::error!(
        "[Proto Dumper] cannot find `{RSP_NOTIFY_DICT_TYPE}` CmdId dictionary; ScRsp/Notify CmdIds will be missing"
    );
    HashMap::new()
}

fn get_req_method_va_name_map() -> HashMap<usize, String> {
    let mut output = HashMap::new();

    let mappings = disasm_obf_deobf_method_by_xlua_obj_translator();
    let mut unique_methods = HashMap::<Cow<'static, str>, Vec<Il2CppMethod>>::new();
    FUNCTIONS_TABLE_REFLECTION
        .get()
        .unwrap()
        .iter()
        .for_each(|v| unique_methods.entry(v.1.get_name()).or_default().push(*v.1));

    for (obf, deobf) in mappings {
        if !deobf.ends_with("Req") {
            continue;
        }

        let Some(methods) = unique_methods.get(&Cow::Borrowed(obf.as_str())) else {
            continue;
        };

        for method in methods {
            if XLUA_OBJECT_TRANSLATOR_METHOD_CLASS
                .as_ref()
                .is_ok_and(|class| method.class().byval_arg().il_name() == *class)
            {
                continue;
            }

            output.insert(method.va(), deobf.clone());
        }
    }

    output
}

struct XLuaAnchors {
    delegate_type_rva: usize,
    obj_translator_fields: HashMap<usize, String>,
    register_object_rva: usize,
}

fn resolve_xlua_anchors() -> Result<XLuaAnchors, String> {
    let delegate_name = XLUA_OBJECT_TRANSLATOR_DELEGATE.clone()?;
    let static_fields_name = XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS.clone()?;
    let register_object_rva = XLUA_REGISTER_OBJECT_RVA.clone()?;

    let delegate_class = get_cached_class(&delegate_name)
        .ok_or_else(|| format!("delegate class `{delegate_name}` not found"))?;
    let delegate_type_rva = *TYPE_INFOS
        .get()
        .ok_or("TYPE_INFOS is not initialized")?
        .get(&delegate_class)
        .ok_or_else(|| format!("no TypeInfo RVA for `{delegate_name}`"))?;

    let obj_translator_fields = get_cached_class(&static_fields_name)
        .ok_or_else(|| format!("class `{static_fields_name}` not found"))?
        .get_fields()
        .into_iter()
        .filter_map(|v| {
            let field_name = FieldInfo::from_il2cpp_field(v).ok()?.get_name().ok()?;
            let field_name = field_name.as_str();
            let (_, rest) = field_name.split_once("__")?;
            Some((v.offset(), strip_prefixes(rest, &["Send"]).to_string()))
        })
        .collect::<HashMap<_, _>>();

    if obj_translator_fields.is_empty() {
        return Err(format!(
            "`{static_fields_name}` has no `__`-prefixed static fields"
        ));
    }

    Ok(XLuaAnchors {
        delegate_type_rva,
        obj_translator_fields,
        register_object_rva,
    })
}

fn disasm_obf_deobf_method_by_xlua_obj_translator() -> HashMap<String, String> {
    let mut output = HashMap::new();

    let XLuaAnchors {
        delegate_type_rva,
        obj_translator_fields,
        register_object_rva: xlua_register_object_rva,
    } = match resolve_xlua_anchors() {
        Ok(anchors) => anchors,
        Err(err) => {
            log::error!("[Proto Dumper] xLua name recovery disabled: {err}");
            return output;
        }
    };

    let mut decoder = Decoder::with_ip(
        64,
        crate::proto::util::code_slice(xlua_register_object_rva, None),
        *GA_BASE as u64 + xlua_register_object_rva as u64,
        DecoderOptions::NONE,
    );

    let mut instructions = VecDeque::<Instruction>::with_capacity(500);
    let mut instruction = Instruction::default();

    let mut static_field_offset = None;
    let mut push_cnt = 0;
    let mut past_prologue = false;

    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);

        if instruction.mnemonic() == Mnemonic::Push {
            if past_prologue {
                push_cnt += 1;

                if push_cnt > 4 {
                    break;
                }
            }
        } else {
            past_prologue = true;
        }

        // mov rcx, cs:XLUA_DELEGATE_TYPE_INFO_VA
        if instruction.mnemonic() == Mnemonic::Mov
            && instruction.op0_register() == Register::RCX
            && instruction.op1_kind() == OpKind::Memory
            && instruction.memory_displacement64() == (delegate_type_rva + *il2cpp::GA_BASE) as u64
        {
            // traverse to find the displacement register
            let mut found_offset = None;
            for i in (0..instructions.len()).rev() {
                let inst = instructions[i];

                if inst.mnemonic() != Mnemonic::Mov {
                    continue;
                }

                let offset = (is_gp64_register(inst.op0_register())
                    && inst.op1_kind() == OpKind::Memory
                    || inst.op0_kind() == OpKind::Memory)
                    .then(|| inst.memory_displacement64());

                let Some(offset) = offset else {
                    continue;
                };

                if obj_translator_fields.contains_key(&(offset as usize)) {
                    found_offset = Some(offset);
                    break;
                }
            }

            if let Some(offset) = found_offset {
                static_field_offset = Some(offset);
            }

            continue;
        }

        // static_field_offset already set
        // call to il2cpp_object_new
        let il2cpp_object_new_rva = *IL2CPP_OBJECT_NEW_RVA;
        if let Some(offset) = static_field_offset
            && instruction.mnemonic() == Mnemonic::Call
            && instruction.near_branch_target() == (*il2cpp::GA_BASE + il2cpp_object_new_rva) as u64
        {
            decoder.decode_out(&mut instruction); // skip mov rsi, rax
            decoder.decode_out(&mut instruction);

            // mov rax, cs::METHOD_INFO_VA
            if instruction.mnemonic() == Mnemonic::Mov && instruction.op1_kind() == OpKind::Memory {
                let type_va = instruction.memory_displacement64() as usize;

                let method = unsafe { *(type_va as *const Il2CppMethod) };
                if method.0 == 0 {
                    static_field_offset = None;
                    continue;
                }

                let Some(field_name) = obj_translator_fields.get(&(offset as usize)) else {
                    static_field_offset = None;
                    continue;
                };

                let name = method.get_name();

                output.insert(name.to_string(), field_name.to_string());
                static_field_offset = None;
            }

            continue;
        }

        instructions.push_back(instruction);
    }

    log::debug!(
        "[Proto Dumper] xLua obf->deobf method names: {}",
        output.len()
    );
    output
}

pub fn get_req_map(
    minimal_info: &HashMap<RuntimeType, MessageMinimalInfo>,
    rsp_notify_map: &HashMap<RuntimeType, u16>,
    req_map: &mut HashMap<RuntimeType, (u16, Option<String>)>,
) -> HashMap<RuntimeType, Vec<String>> {
    let Some(type_infos) = TYPE_INFOS.get() else {
        log::error!(
            "[Proto Dumper] TYPE_INFOS is not initialized (run the Script dumper first); CsReq CmdIds will be missing"
        );
        return HashMap::new();
    };
    let type_info_rvas = minimal_info
        .iter()
        .filter(|(ty, _)| {
            !ty.get_isenum().is_ok_and(|v| v.unbox()) && !rsp_notify_map.contains_key(ty)
        })
        .filter_map(|(ty, _)| type_infos.get(&ty.get_il2cpp_type().get_class()).copied())
        .collect::<HashSet<_>>();

    let mut targets = HashMap::with_capacity(3);

    match NETWORK_MANAGER_SEND_NAME.as_ref() {
        Ok(name) => {
            let signature = format!(
                "RPG.Client.NetworkManager::{name}(System.UInt16,Google.Protobuf.IMessage,System.Boolean)"
            );
            match get_native_method(&signature) {
                Some(method) => {
                    targets.insert(method.va(), ReqFlavor::Standard);
                }
                None => log::error!("[Proto Dumper] native method `{signature}` not found"),
            }
        }
        Err(_) => log::warn!("[Proto Dumper] NetworkManager::Send unavailable, skipping it"),
    }
    if let Ok(va) = *NETWORK_MANAGER_SEND_VA {
        targets.insert(va, ReqFlavor::Standard);
    }
    if let Ok(va) = *FIGHT_GAME_SEND {
        targets.insert(va, ReqFlavor::Fight);
    }

    if targets.is_empty() {
        log::error!("[Proto Dumper] no Send function resolved; CsReq CmdIds will be missing");
        return HashMap::new();
    }
    log::debug!(
        "[Proto Dumper] scanning GameAssembly for calls to {} Send function(s): [{}], req type infos={}, il2cpp_object_new=0x{:X}",
        targets.len(),
        targets
            .iter()
            .map(|(va, flavor)| format!("0x{:X} {flavor:?}", va.wrapping_sub(*GA_BASE)))
            .collect::<Vec<_>>()
            .join(", "),
        type_info_rvas.len(),
        *IL2CPP_OBJECT_NEW_RVA
    );

    let result = disasm_all_req(&type_info_rvas, targets, rsp_notify_map, req_map);
    if req_map.is_empty() {
        log::error!(
            "[Proto Dumper] Send call sites were scanned but no CsReq CmdId was recovered; the call-site register pattern may have changed"
        );
    }
    result
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
enum ReqFlavor {
    Standard, // DX, R8
    Fight,    // R8, R9
}

const MAX_UNMATCHED_SAMPLES: usize = 16;

#[derive(Default)]
struct ReqScanStats {
    call_sites: usize,
    with_cmd_id: usize,
    with_object: usize,
    identified: usize,
    unmatched_samples: Vec<String>,
}

fn is_cmd_id_register(flavor: ReqFlavor, reg: Register) -> bool {
    match flavor {
        ReqFlavor::Standard => matches!(reg, Register::DX | Register::EDX | Register::RDX),
        ReqFlavor::Fight => matches!(reg, Register::R8W | Register::R8D | Register::R8),
    }
}

fn immediate_cmd_id(inst: &Instruction) -> Option<u16> {
    match inst.op1_kind() {
        OpKind::Immediate8
        | OpKind::Immediate16
        | OpKind::Immediate32
        | OpKind::Immediate64
        | OpKind::Immediate8to16
        | OpKind::Immediate8to32
        | OpKind::Immediate8to64
        | OpKind::Immediate32to64 => u16::try_from(inst.immediate(1)).ok(),
        _ => None,
    }
}

fn disasm_all_req(
    type_info_rvas: &HashSet<usize>,
    targets: HashMap<usize, ReqFlavor>,
    rsp_notify_map: &HashMap<RuntimeType, u16>,
    out: &mut HashMap<RuntimeType, (u16, Option<String>)>,
) -> HashMap<RuntimeType, Vec<String>> {
    let va_deobf_map = get_req_method_va_name_map();
    let slice = game_assembly_slice();
    let mut decoder = Decoder::with_ip(64, slice, *GA_BASE as u64, DecoderOptions::NONE);

    let mut instruction = Instruction::default();
    let mut instructions = VecDeque::<Instruction>::with_capacity(500);
    let mut req_rvas: HashMap<RuntimeType, Vec<String>> = HashMap::new();

    #[derive(Debug, Eq, PartialEq, Clone, Copy)]
    enum InstType {
        Memory { base: Register, displacement: i64 },
        Normal(Register),
    }

    impl InstType {
        pub fn new(op_kind: OpKind, reg: Register, memory: Register, displacement: i64) -> Self {
            if op_kind == OpKind::Memory {
                Self::Memory {
                    base: memory,
                    displacement,
                }
            } else {
                Self::Normal(reg)
            }
        }
        pub fn is_rax(&self) -> bool {
            match self {
                InstType::Memory { base, .. } => *base == Register::RAX,
                InstType::Normal(register) => *register == Register::RAX,
            }
        }
        pub fn is_none(&self) -> bool {
            match self {
                InstType::Memory { base, .. } => *base == Register::None,
                InstType::Normal(register) => *register == Register::None,
            }
        }
    }

    type CandidateInfo = (HashSet<u16>, HashSet<Option<String>>, Vec<String>);
    let mut candidates: HashMap<RuntimeType, CandidateInfo> = HashMap::new();
    let mut cur_func_va = None;
    let mut stats = ReqScanStats::default();

    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);

        if instruction.mnemonic() == Mnemonic::Push
            && let Some(prev) = instructions.back()
            && prev.mnemonic() != Mnemonic::Push
        {
            cur_func_va = Some(instruction.ip());
            instructions.clear();
        }

        if (instruction.mnemonic() == Mnemonic::Jmp || instruction.mnemonic() == Mnemonic::Call)
            && let Some(&flavor) = targets.get(&(instruction.near_branch_target() as usize))
        {
            let mut obj_register = None;
            let mut cmd_id = None;
            let mut push_rva = None;
            let mut last_push_index = None;
            let mut identified = false;
            stats.call_sites += 1;

            let mut i = instructions.len();
            while i > 0 {
                i -= 1;
                if instructions[i].mnemonic() == Mnemonic::Push {
                    last_push_index = Some(i);
                } else if last_push_index.is_some() {
                    break;
                }
            }
            if let Some(push_index) = last_push_index {
                push_rva = Some((instructions[push_index].ip() as usize).wrapping_sub(*GA_BASE));
            }

            for i in (0..instructions.len()).rev() {
                let inst = instructions[i];
                if inst.mnemonic() == Mnemonic::Push {
                    break;
                }

                // 1: CmdId
                if cmd_id.is_none() && inst.mnemonic() == Mnemonic::Mov {
                    if is_cmd_id_register(flavor, inst.op0_register())
                        && let Some(id) = immediate_cmd_id(&inst)
                        && id != 0
                        && !rsp_notify_map.values().any(|&v| v == id)
                    {
                        cmd_id = Some(id);
                    }
                    if cmd_id.is_some() {
                        continue;
                    }
                }

                // 2: Object Register
                if obj_register.is_none() && inst.mnemonic() == Mnemonic::Mov {
                    let reg = inst.op0_register();
                    let is_match = match flavor {
                        ReqFlavor::Standard => reg == Register::R8,
                        ReqFlavor::Fight => reg == Register::R9,
                    };
                    if is_match {
                        obj_register = Some(InstType::new(
                            inst.op1_kind(),
                            inst.op1_register(),
                            inst.memory_base(),
                            inst.memory_displacement64() as i64,
                        ));
                        continue;
                    }
                }

                // 3: register
                if let Some(reg) = obj_register
                    && inst.mnemonic() == Mnemonic::Mov
                    && (InstType::new(
                        inst.op0_kind(),
                        inst.op0_register(),
                        inst.memory_base(),
                        inst.memory_displacement64() as i64,
                    ) == reg)
                    && !reg.is_rax()
                {
                    let new = InstType::new(
                        inst.op1_kind(),
                        inst.op1_register(),
                        inst.memory_base(),
                        inst.memory_displacement64() as i64,
                    );
                    if !new.is_none() {
                        obj_register = Some(new);
                    }
                    continue;
                }

                // 4: Identification
                if let Some(cmd_id) = cmd_id
                    && let Some(reg) = obj_register
                {
                    // A: il2cpp_object_new
                    if reg.is_rax()
                        && (inst.mnemonic() == Mnemonic::Call || inst.mnemonic() == Mnemonic::Jmp)
                    {
                        let target_va = inst.near_branch_target() as usize;
                        if target_va.wrapping_sub(*GA_BASE) == *IL2CPP_OBJECT_NEW_RVA
                            && let Some(prev) = i.checked_sub(1).map(|p| instructions[p])
                        {
                            let va = prev.memory_displacement64() as usize;
                            if type_info_rvas.contains(&va.wrapping_sub(*GA_BASE)) {
                                let class = unsafe { *(va as *const Il2CppClass) };
                                if let Ok(rt) = RuntimeType::from_class(class) {
                                    let deobf_name = cur_func_va
                                        .and_then(|v| va_deobf_map.get(&(v as usize)).cloned());
                                    let entry = candidates.entry(rt).or_insert_with(|| {
                                        (HashSet::new(), HashSet::new(), Vec::new())
                                    });
                                    entry.0.insert(cmd_id);
                                    entry.1.insert(deobf_name);
                                    if let Some(prva) = push_rva {
                                        entry.2.push(format!("0x{prva:X}"));
                                    }
                                    identified = true;
                                    break;
                                }
                            }
                        }
                    }

                    // B: Cmp
                    if flavor == ReqFlavor::Standard
                        && inst.mnemonic() == Mnemonic::Cmp
                        && inst.op0_kind() == OpKind::Memory
                        && inst.memory_base()
                            == match reg {
                                InstType::Normal(r) => r,
                                InstType::Memory { base, .. } => base,
                            }
                    {
                        let type_info_reg = inst.op1_register();
                        if type_info_reg != Register::None {
                            for j in (0..i).rev() {
                                let prev = instructions[j];
                                if prev.mnemonic() == Mnemonic::Mov
                                    && prev.op0_register() == type_info_reg
                                {
                                    let va = prev.memory_displacement64() as usize;
                                    if type_info_rvas.contains(&va.wrapping_sub(*GA_BASE)) {
                                        let class = unsafe { *(va as *const Il2CppClass) };
                                        if let Ok(rt) = RuntimeType::from_class(class) {
                                            let deobf_name = cur_func_va.and_then(|v| {
                                                va_deobf_map.get(&(v as usize)).cloned()
                                            });
                                            let entry = candidates.entry(rt).or_insert_with(|| {
                                                (HashSet::new(), HashSet::new(), Vec::new())
                                            });
                                            entry.0.insert(cmd_id);
                                            entry.1.insert(deobf_name);
                                            if let Some(prva) = push_rva {
                                                entry.2.push(format!("0x{prva:X}"));
                                            }
                                            identified = true;
                                            break;
                                        }
                                    }
                                }
                            }
                            if candidates.values().any(|v| v.0.contains(&cmd_id)) {
                                break;
                            }
                        }
                    }
                }
            }
            if cmd_id.is_some() {
                stats.with_cmd_id += 1;
            }
            if obj_register.is_some() {
                stats.with_object += 1;
            }
            if identified {
                stats.identified += 1;
            } else if stats.unmatched_samples.len() < MAX_UNMATCHED_SAMPLES {
                stats.unmatched_samples.push(format!(
                    "0x{:X}(cmd_id={}, object={})",
                    (instruction.ip() as usize).wrapping_sub(*GA_BASE),
                    cmd_id.map_or_else(|| "-".to_string(), |id| id.to_string()),
                    obj_register.is_some()
                ));
            }
        }
        if instructions.len() >= 500 {
            instructions.pop_front();
        }
        instructions.push_back(instruction);
    }

    log::debug!(
        "[Proto Dumper] Send call sites: total={}, with_cmd_id={}, with_object={}, identified={}, distinct_types={}",
        stats.call_sites,
        stats.with_cmd_id,
        stats.with_object,
        stats.identified,
        candidates.len()
    );
    if !stats.unmatched_samples.is_empty() {
        log::warn!(
            "[Proto Dumper] unmatched Send call sites (first {}): {}",
            stats.unmatched_samples.len(),
            stats.unmatched_samples.join(", ")
        );
    }

    for (rt, (ids, names, rvas)) in candidates {
        if ids.len() == 1 {
            out.insert(
                rt,
                (
                    *ids.iter().next().unwrap(),
                    names.into_iter().flatten().next(),
                ),
            );
            req_rvas.insert(rt, rvas);
        }
    }
    req_rvas
}

pub fn get_rsp_notify_names() -> HashMap<String, String> {
    let Some(cached_methods) = FUNCTIONS_TABLE_REFLECTION.get() else {
        log::error!(
            "[Proto Dumper] FUNCTIONS_TABLE_REFLECTION is not initialized, skipping rsp/notify names"
        );
        return HashMap::new();
    };
    let prefixes_to_replace = ["_OnCmd", "_Cmd", "_On", "OnCmd", "On", "Cmd"];

    let mut nt_map = HashMap::new();

    for (m_name, m) in cached_methods {
        if !m_name.ends_with("(System.UInt16,System.Object)") {
            continue;
        }

        let Some(proto_class) = disasm_rsp_notify_3_args(m.rva()) else {
            continue;
        };

        let m_name = m.get_name();
        for prefix in prefixes_to_replace {
            if let Some(name) = m_name.strip_prefix(prefix) {
                let _ = microseh::try_seh(|| {
                    nt_map.insert(
                        RuntimeType::from_class(proto_class)
                            .unwrap()
                            .format_type_name(true),
                        name.to_string()
                            .replace("Cmd", "")
                            .replace("ScRep", "ScRsp"),
                    );
                });
            }
        }
    }

    nt_map
}

pub fn get_rsp_notify_method_rvas() -> HashMap<String, Vec<String>> {
    let Some(cached_methods) = FUNCTIONS_TABLE_REFLECTION.get() else {
        log::error!(
            "[Proto Dumper] FUNCTIONS_TABLE_REFLECTION is not initialized, skipping rsp/notify handlers"
        );
        return HashMap::new();
    };
    let prefixes_to_replace = ["_OnCmd", "_Cmd", "_On", "OnCmd", "On", "Cmd"];

    let mut rva_map: HashMap<String, Vec<String>> = HashMap::new();

    for (m_name, m) in cached_methods {
        if !m_name.ends_with("(System.UInt16,System.Object)") {
            continue;
        }

        let Some(proto_class) = disasm_rsp_notify_3_args(m.rva()) else {
            continue;
        };

        let m_name_str = m.get_name();
        for prefix in prefixes_to_replace {
            if m_name_str.starts_with(prefix) {
                let _ = microseh::try_seh(|| {
                    let formatted_name = RuntimeType::from_class(proto_class)
                        .unwrap()
                        .format_type_name(true)
                        .replace("ScRep", "ScRsp");

                    rva_map
                        .entry(formatted_name)
                        .or_default()
                        .push(format!("0x{:X}", m.rva()));
                });
                break;
            }
        }
    }

    rva_map
}

fn disasm_rsp_notify_3_args(rva: usize) -> Option<Il2CppClass> {
    let mut decoder = Decoder::with_ip(
        64,
        crate::proto::util::code_slice(rva, None),
        (*GA_BASE + rva) as u64,
        DecoderOptions::NONE,
    );

    let mut instruction = Instruction::default();

    let mut is_passing_push = false;
    let mut current_r8_reg = Register::R8;
    let mut current_dereferenced_reg = None;

    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);

        // Move current r8 reg into another reg
        // mov new_current_r8_reg, current_r8_reg
        if instruction.mnemonic() == Mnemonic::Mov && instruction.op1_register() == current_r8_reg {
            current_r8_reg = instruction.op0_register();
            is_passing_push = true;
        }

        // detect if current_r8_reg is being dereferenced
        // mov current_dereferenced_reg, [current_r8_reg]
        if instruction.op1_kind() == OpKind::Memory && instruction.memory_base() == current_r8_reg {
            current_dereferenced_reg = Some(instruction.op0_register());
        }

        // cmp current_dereferenced_reg, cs:PROTO_TYPE
        if instruction.mnemonic() == Mnemonic::Cmp
            && let Some(reg) = current_dereferenced_reg
            && instruction.op0_register() == reg
            && instruction.op1_kind() == OpKind::Memory
        {
            let va = instruction.memory_displacement64() as usize;
            match microseh::try_seh(|| {
                let class = unsafe { *(va as *const Il2CppClass) };
                if class.0 != 0 { Some(class) } else { None }
            }) {
                Ok(data) => return data,
                Err(_err) => {
                    return None;
                }
            }
        }

        // already out of current sub_
        if is_passing_push && instruction.mnemonic() == Mnemonic::Push {
            break;
        }
    }

    None
}

fn strip_prefixes<'a>(s: &'a str, prefixes: &[&str]) -> &'a str {
    for p in prefixes {
        if let Some(rest) = s.strip_prefix(p) {
            return rest;
        }
    }
    s
}

fn is_gp64_register(register: Register) -> bool {
    matches!(
        register,
        Register::RAX
            | Register::RCX
            | Register::RDX
            | Register::RBX
            | Register::RSP
            | Register::RBP
            | Register::RSI
            | Register::RDI
            | Register::R8
            | Register::R9
            | Register::R10
            | Register::R11
            | Register::R12
            | Register::R13
            | Register::R14
            | Register::R15
    )
}
