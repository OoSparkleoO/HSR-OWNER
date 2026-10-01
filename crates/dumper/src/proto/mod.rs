use std::{borrow::Cow, collections::HashMap, io::Write, panic::AssertUnwindSafe, sync::LazyLock};

use anyhow::Context;
use cache::{CachedType, TypeCache};
use iced_x86::{Decoder, DecoderOptions, Instruction, Mnemonic};
use il2cpp::{
    CLASS_TABLE_VEC, get_cached_class, get_native_method,
    vm::{metadata_cache, value::Il2CppValue},
};
use reflection::{method_info::MethodInfo, property_info::PropertyInfo, runtime_type::RuntimeType};
use utils::game_assembly_slice;

mod cache;
pub mod handler_nt;
mod logic_nt;
mod merge_from;
mod method_nt;
mod nt;
mod output;
mod proto_asm_parser;
mod proto_stream;
pub mod util;
mod write_to;

/// Result of resolving a runtime anchor (class / method / address the dumper depends on).
/// Failures are logged once and degrade the affected output instead of hanging the dumper.
pub type AnchorResult<T> = Result<T, String>;

fn resolve_anchor<T>(name: &str, resolve: impl FnOnce() -> AnchorResult<T>) -> AnchorResult<T> {
    let result = std::panic::catch_unwind(AssertUnwindSafe(resolve))
        .unwrap_or_else(|payload| Err(format!("panicked: {}", util::panic_message(&*payload))));
    if let Err(err) = &result {
        log::error!("[Proto Dumper] failed to resolve {name}: {err}");
    }
    result
}

fn find_class(name: &str) -> AnchorResult<il2cpp::api::Il2CppClass> {
    get_cached_class(name).ok_or_else(|| format!("class `{name}` not found in class cache"))
}

fn runtime_type_of(name: &str) -> AnchorResult<RuntimeType> {
    RuntimeType::from_class(find_class(name)?)
        .map_err(|_| format!("failed to create RuntimeType for `{name}`"))
}

/// Typedef index of the class right before `class_name` in the class table.
fn previous_class_name(class_name: &str) -> AnchorResult<Cow<'static, str>> {
    let class = find_class(class_name)?;
    let idx = CLASS_TABLE_VEC
        .get()
        .ok_or("CLASS_TABLE_VEC is not initialized")?
        .iter()
        .position(|&v| v == class)
        .ok_or_else(|| format!("`{class_name}` not found in CLASS_TABLE_VEC"))?;
    let prev_idx = idx
        .checked_sub(1)
        .ok_or_else(|| format!("`{class_name}` is the first entry of CLASS_TABLE_VEC"))?;
    let name = metadata_cache::get_typeinfo_from_typedefindex(prev_idx as u32)
        .byval_arg()
        .il_name();
    if name.is_empty() {
        return Err(format!(
            "class before `{class_name}` (typedef index {prev_idx}) has an empty name; the class layout may have changed"
        ));
    }
    Ok(name)
}

const IL2CPP_OBJECT_NEW_API_INDEX: usize = 130;

static IL2CPP_OBJECT_NEW_API_RVA: LazyLock<AnchorResult<usize>> = LazyLock::new(|| {
    resolve_anchor("il2cpp_object_new API", || {
        let api_addr = microseh::try_seh(|| unsafe {
            let api_ptr_addr = (*il2cpp::API_BASE_PTR) + 8 * IL2CPP_OBJECT_NEW_API_INDEX;
            *((*il2cpp::UP_BASE + api_ptr_addr) as *const usize)
        })
        .map_err(|err| format!("reading il2cpp API table faulted: {err:?}"))?;

        let ga_len = game_assembly_slice().len();
        api_addr
            .checked_sub(*il2cpp::GA_BASE)
            .filter(|rva| *rva < ga_len)
            .ok_or_else(|| {
                format!(
                    "API table entry #{IL2CPP_OBJECT_NEW_API_INDEX} (0x{api_addr:X}) does not point into GameAssembly; the API table layout may have changed"
                )
            })
    })
});

/// RVA of the real `il2cpp_object_new` implementation, or 0 when it cannot be located
/// (0 never matches a call target, so dependent heuristics simply find nothing).
static IL2CPP_OBJECT_NEW_RVA: LazyLock<usize> = LazyLock::new(|| {
    let Ok(api_rva) = *IL2CPP_OBJECT_NEW_API_RVA else {
        return 0;
    };
    let mut decoder = Decoder::with_ip(
        64,
        util::code_slice(api_rva, Some(0x80)),
        (*il2cpp::GA_BASE + api_rva) as u64,
        DecoderOptions::NONE,
    );
    let mut instruction = Instruction::default();
    while decoder.can_decode() {
        decoder.decode_out(&mut instruction);
        if instruction.mnemonic() == Mnemonic::Call {
            let real_rva =
                (instruction.near_branch_target() as usize).wrapping_sub(*il2cpp::GA_BASE);
            log::debug!("[Proto Dumper] Il2CppObject::New => 0x{real_rva:X}");
            return real_rva;
        }
        if instruction.mnemonic() == Mnemonic::Ret || instruction.mnemonic() == Mnemonic::Int3 {
            break;
        }
    }
    log::warn!(
        "[Proto Dumper] no call found in il2cpp_object_new API stub at 0x{api_rva:X}, using the API rva itself"
    );
    api_rva
});

static XLUA_REGISTER_OBJECT_RVA: LazyLock<AnchorResult<usize>> = LazyLock::new(|| {
    resolve_anchor("XLua::RegisterObject", || {
        let raw_class_name = XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS.clone()?;
        let class_name = raw_class_name
            .split('<')
            .next()
            .unwrap_or_default()
            .trim_end_matches('.');
        let static_class_type = runtime_type_of(class_name)?;
        let delegate_name = XLUA_OBJECT_TRANSLATOR_DELEGATE.clone()?;

        let methods = static_class_type.get_methods_il2cpp();
        let next = methods
            .iter()
            .position(|method| {
                let params = method.get_parameters();
                params.len() == 1
                    && params[0]
                        .get_parameter_type()
                        .is_ok_and(|ty| ty.il_name() == delegate_name)
            })
            .ok_or_else(|| {
                format!("no method of `{class_name}` takes a single `{delegate_name}` parameter")
            })
            .and_then(|idx| {
                methods.get(idx + 1).ok_or_else(|| {
                    format!("method taking `{delegate_name}` is the last method of `{class_name}`")
                })
            })?;

        let va = next.get_il2cpp_method().va();
        let rva = va
            .checked_sub(*il2cpp::GA_BASE)
            .ok_or_else(|| format!("method VA 0x{va:X} is below GameAssembly base"))?;
        log::debug!("[Proto Dumper] XLua::RegisterObject => 0x{rva:X}");
        Ok(rva)
    })
});

static RETCODE_FIELD_NAME: LazyLock<AnchorResult<Cow<'static, str>>> = LazyLock::new(|| {
    resolve_anchor("MsgRetcode field name", || {
        let cake_race_type =
            runtime_type_of("RPG.Client.LittleGame.CakeRace.CakeRaceBaseRspMessage<T>")?;
        let base_type = cake_race_type
            .get_base_type()
            .map_err(|_| "CakeRaceBaseRspMessage<T> has no base type".to_string())?;

        let properties = base_type.get_properties(62);
        let property = properties.first().ok_or_else(|| {
            format!(
                "there are no properties in {} to get MsgRetcode",
                base_type
                    .get_il2cpp_type()
                    .get_class()
                    .byval_arg()
                    .il_name()
            )
        })?;

        let property_name = property
            .get_name()
            .map_err(|_| "failed to read retcode property name".to_string())?
            .as_str();
        log::debug!("[Proto Dumper] retcode => {property_name}");
        Ok(property_name)
    })
});

pub fn is_retcode_field(name: &str) -> bool {
    RETCODE_FIELD_NAME
        .as_ref()
        .is_ok_and(|retcode| retcode == name)
}

/// Concrete metadata method behind the generic 3-arg `NetworkManager::Send<T>`
/// declared on `CycleScoreService`'s base type.
fn find_network_manager_generic_send() -> AnchorResult<MethodInfo> {
    let cycle_score_service = runtime_type_of("RPG.Client.CycleScoreService")?;
    let the_class = cycle_score_service
        .get_base_type()
        .map_err(|_| "RPG.Client.CycleScoreService has no base type".to_string())?;
    let metadata_methods = crate::script::METADATA_METHODS
        .get()
        .ok_or("script METADATA_METHODS is not initialized (script metadata must load first)")?;

    for method in the_class.get_methods_il2cpp() {
        if !method.get_is_generic_method().is_ok_and(|v| v.unbox()) {
            continue;
        }
        if method.get_parameters().len() != 3 {
            continue;
        }
        if let Some(m_method) = metadata_methods
            .get(&the_class.get_metadata_token())
            .and_then(|m| m.get(&method.get_metadata_token()))
            .and_then(|m| m.first())
        {
            return Ok(*m_method);
        }
    }

    Err(format!(
        "no generic 3-parameter Send method with metadata found on `{}`",
        the_class.il_name()
    ))
}

pub static NETWORK_MANAGER_SEND_NAME: LazyLock<AnchorResult<Cow<'static, str>>> =
    LazyLock::new(|| {
        resolve_anchor("NetworkManager::Send name", || {
            let method_name = find_network_manager_generic_send()?
                .get_name()
                .map_err(|_| "failed to read NetworkManager::Send name".to_string())?
                .as_str();
            log::debug!("[Proto Dumper] NetworkManager::Send => {method_name}");
            Ok(method_name)
        })
    });

pub static NETWORK_MANAGER_SEND_VA: LazyLock<AnchorResult<usize>> = LazyLock::new(|| {
    resolve_anchor("NetworkManager::Send2", || {
        let va = find_network_manager_generic_send()?
            .get_il2cpp_method()
            .va();
        log::debug!(
            "[Proto Dumper] NetworkManager::Send2 => 0x{:X}",
            va.wrapping_sub(*il2cpp::GA_BASE)
        );
        Ok(va)
    })
});

pub static FIGHT_GAME_SEND: LazyLock<AnchorResult<usize>> = LazyLock::new(|| {
    resolve_anchor("FightGame::Send", || {
        let multiplayer_manager = runtime_type_of("RPG.Client.GlobalVars")?
            .get_field("s_MultiplayerManager".into(), 62)
            .map_err(|_| "RPG.Client.GlobalVars::s_MultiplayerManager not found".to_string())?;
        if multiplayer_manager.is_null() {
            return Err("RPG.Client.GlobalVars::s_MultiplayerManager not found".into());
        }

        let multiplayer_manager = multiplayer_manager
            .get_field_type()
            .map_err(|_| "failed to read s_MultiplayerManager field type".to_string())?;

        let methods = multiplayer_manager.get_methods_il2cpp();
        for method in &methods {
            let params = method.get_parameters();
            if params.len() >= 3
                && params[1]
                    .get_parameter_type()
                    .is_ok_and(|ty| ty.il_name() == "System.UInt16")
            {
                let va = method.get_il2cpp_method().va();
                if let Ok(name) = method.get_name() {
                    log::debug!("[Proto Dumper] FightGame::Send => {}", name.as_str());
                }
                return Ok(va);
            }
        }

        let signatures = methods
            .iter()
            .filter(|method| {
                method.get_parameters().iter().any(|param| {
                    param
                        .get_parameter_type()
                        .is_ok_and(|ty| ty.il_name() == "System.UInt16")
                })
            })
            .map(|method| {
                let name = method
                    .get_name()
                    .map_or_else(|_| "<unknown>".to_string(), |n| n.as_str().to_string());
                let params = method
                    .get_parameters()
                    .iter()
                    .map(|param| {
                        param
                            .get_parameter_type()
                            .map_or_else(|_| "?".to_string(), |ty| ty.il_name().to_string())
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({params})")
            })
            .collect::<Vec<_>>();
        Err(format!(
            "no `(_, System.UInt16, _, ...)` method on `{}` ({} methods); methods taking UInt16: [{}]",
            multiplayer_manager.il_name(),
            methods.len(),
            signatures.join("; ")
        ))
    })
});

static XLUA_OBJECT_TRANSLATOR_DELEGATE: LazyLock<AnchorResult<Cow<'static, str>>> =
    LazyLock::new(|| {
        resolve_anchor("XLUA_OBJECT_TRANSLATOR_DELEGATE", || {
            let name = previous_class_name(&XLUA_OBJECT_TRANSLATOR_METHOD_CLASS.clone()?)?;
            log::debug!("[Proto Dumper] XLUA_OBJECT_TRANSLATOR_DELEGATE => {name}");
            Ok(name)
        })
    });

static XLUA_OBJECT_TRANSLATOR_METHOD_CLASS: LazyLock<AnchorResult<Cow<'static, str>>> =
    LazyLock::new(|| {
        resolve_anchor("XLUA_OBJECT_TRANSLATOR_METHOD_CLASS", || {
            let name = previous_class_name(&XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS.clone()?)?;
            log::debug!("[Proto Dumper] XLUA_OBJECT_TRANSLATOR_METHOD_CLASS => {name}");
            Ok(name)
        })
    });

static XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS: LazyLock<AnchorResult<Cow<'static, str>>> =
    LazyLock::new(|| {
        resolve_anchor("XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS", || {
            let name = previous_class_name("XLua.CSObjectWrap.Gen_13_Wrap")?;
            log::debug!("[Proto Dumper] XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS => {name}");
            Ok(name)
        })
    });

/// Forces every anchor and logs a summary of the ones that failed together with
/// the output they affect, so a broken game update is easy to diagnose.
fn report_anchors() -> usize {
    let checks: [(&str, bool, &str); 8] = [
        (
            "il2cpp_object_new API",
            IL2CPP_OBJECT_NEW_API_RVA.is_ok(),
            "CsReq CmdIds, handler field names",
        ),
        (
            "MsgRetcode field name",
            RETCODE_FIELD_NAME.is_ok(),
            "Rsp/Notify classification, `retcode` field naming",
        ),
        (
            "NetworkManager::Send name",
            NETWORK_MANAGER_SEND_NAME.is_ok(),
            "CsReq CmdIds",
        ),
        (
            "NetworkManager::Send2",
            NETWORK_MANAGER_SEND_VA.is_ok(),
            "CsReq CmdIds",
        ),
        (
            "FightGame::Send",
            FIGHT_GAME_SEND.is_ok(),
            "fight CsReq CmdIds",
        ),
        (
            "XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS",
            XLUA_OBJECT_TRANSLATOR_STATIC_FIELDS_CLASS.is_ok(),
            "CsReq names from xLua",
        ),
        (
            "XLUA_OBJECT_TRANSLATOR_DELEGATE",
            XLUA_OBJECT_TRANSLATOR_DELEGATE.is_ok(),
            "CsReq names from xLua",
        ),
        (
            "XLua::RegisterObject",
            XLUA_REGISTER_OBJECT_RVA.is_ok(),
            "CsReq names from xLua",
        ),
    ];

    let failed = checks.iter().filter(|(_, ok, _)| !ok).collect::<Vec<_>>();
    for (name, _, impact) in &failed {
        log::warn!("[Proto Dumper] anchor `{name}` unresolved, affected output: {impact}");
    }
    if failed.is_empty() {
        log::debug!("[Proto Dumper] all anchors resolved");
    } else {
        log::warn!(
            "[Proto Dumper] {}/{} anchors unresolved, dump will continue with degraded output (see errors above)",
            failed.len(),
            checks.len()
        );
    }
    failed.len()
}

const CODED_INPUT_STREAM: &str = "Google.Protobuf.CodedInputStream";
const MERGE_FROM: &str = "MergeFrom";
const CODED_OUTPUT_STREAM: &str = "Google.Protobuf.CodedOutputStream";
const WRITE_TO: &str = "WriteTo";
const UNKNOWN_FIELD_SET: &str = "Google.Protobuf.UnknownFieldSet";
const BYTE_STRING: &str = "Google.Protobuf.ByteString";
const PROTOBUF_ANY: &str = "MiHoYo.SDK.Protobuf.WellKnownTypes.Any";
const GET_COUNT_PROPERTY: &str = "Count";

pub struct MessageMinimalInfo {
    #[allow(unused)]
    pub cmd_id: u16,
    pub fields: Vec<FieldMinimalInfo>,
    pub write_to_rva: usize,
    pub merge_from_rva: usize,
}

impl MessageMinimalInfo {
    pub fn new(cmd_id: u16) -> Self {
        Self {
            cmd_id,
            fields: Vec::new(),
            write_to_rva: 0,
            merge_from_rva: 0,
        }
    }
}

pub struct FieldMinimalInfo {
    pub tag: u32,
    #[allow(unused)]
    pub xor: u32,
    pub offset: u32,
    pub oneof_extra_data: Option<OneofVariantInfo>,
    pub number_type: NumberType,
    pub property: Option<PropertyInfo>,
}

#[derive(Clone, Copy)]
pub enum NumberType {
    None,
    Varint,
    Normal,
    #[allow(unused)]
    ZigZagVarint,
}

pub struct OneofVariantInfo {
    pub oneof_enum_offset: u32,
    pub variant_type: RuntimeType,
    pub property: Option<PropertyInfo>,
}

#[allow(dead_code)]
pub enum ProtoDumpMode {
    ClassFieldNumber,
    MergeFrom,
    WriteTo,
    Asm,
}

#[derive(Default)]
struct DumpStats {
    total: usize,
    ok: usize,
    empty: usize,
    skipped: usize,
    panicked: usize,
}

/// Finds the native `WriteTo`/`MergeFrom`/`.ctor` of `proto_name` and runs the selected
/// field discovery algorithm, filling `message_info`.
fn dump_message_info(
    index: u32,
    proto_type: RuntimeType,
    proto_name: &str,
    dump_mode: &ProtoDumpMode,
    type_cache: &TypeCache,
    enable_logging: bool,
    message_info: &mut MessageMinimalInfo,
) -> AnchorResult<()> {
    let write_to_sig = format!("{proto_name}::{WRITE_TO}({CODED_OUTPUT_STREAM})");
    let merge_from_sig = format!("{proto_name}::{MERGE_FROM}({CODED_INPUT_STREAM})");
    let write_to_method = get_native_method(&write_to_sig)
        .ok_or_else(|| format!("native method `{write_to_sig}` not found"))?;
    let merge_from_method = get_native_method(&merge_from_sig)
        .ok_or_else(|| format!("native method `{merge_from_sig}` not found"))?;
    message_info.write_to_rva = write_to_method.rva();
    message_info.merge_from_rva = merge_from_method.rva();

    match dump_mode {
        ProtoDumpMode::ClassFieldNumber => {
            util::generate_minimal_info_from_constants(proto_type, message_info, type_cache);
        }
        ProtoDumpMode::Asm => {
            proto_asm_parser::dump_from_write_to_asm(proto_name, message_info);
        }
        ProtoDumpMode::MergeFrom => {
            let ctor = proto_type
                .find_method_il2cpp(".ctor")
                .ok_or_else(|| format!("`{proto_name}::.ctor` not found"))?;
            let proto_instance = proto_type.get_il2cpp_type().get_class().create_instance();
            ctor.get_il2cpp_method()
                .invoke::<usize>(proto_instance, &[])
                .map_err(|_| format!("`{proto_name}::.ctor` threw a managed exception"))?;
            merge_from::dump_merge_from(proto_type, proto_instance, message_info, type_cache);
        }
        ProtoDumpMode::WriteTo => {
            let ctor_sig = format!("{proto_name}::.ctor()");
            let ctor_method = get_native_method(&ctor_sig)
                .ok_or_else(|| format!("native method `{ctor_sig}` not found"))?;
            write_to::dump_writeto(
                enable_logging,
                index,
                proto_type,
                ctor_method,
                write_to_method,
                message_info,
            );
        }
    }

    Ok(())
}

#[allow(unused)]
pub fn dump<W: Write>(
    out: &mut W,
    cmdid_out: &mut W,
    dump_mode: ProtoDumpMode,
    enable_logging: bool,
) -> anyhow::Result<()> {
    let type_cache = TypeCache::init();
    proto_stream::init();

    report_anchors();

    log::debug!("[Proto Dumper] dumping minimal proto infos...");

    let mut minimal_info_map = HashMap::<RuntimeType, MessageMinimalInfo>::new();
    let mut rsp_notify_map = nt::get_rsp_notify_map();
    let mut req_map = HashMap::<RuntimeType, (u16, Option<String>)>::new();
    let mut stats = DumpStats::default();

    let (proto_start, proto_end) = unsafe {
        (
            il2cpp::RPG_NETWORK_PROTO_START,
            il2cpp::RPG_NETWORK_PROTO_END,
        )
    };
    anyhow::ensure!(
        proto_start < proto_end,
        "proto typedef range is empty ({proto_start}..{proto_end}); RPG.Network.Proto assembly was not located"
    );

    for i in proto_start..proto_end {
        let proto_class = metadata_cache::get_typeinfo_from_typedefindex(i);
        let Ok(proto_type) = RuntimeType::from_class(proto_class) else {
            log::warn!("[Proto Dumper] typedef #{i}: failed to create RuntimeType, skipping");
            continue;
        };

        if proto_type.find_method_il2cpp(MERGE_FROM).is_none() {
            continue;
        }

        let proto_name = proto_type.il_name();
        stats.total += 1;

        if enable_logging {
            log::debug!("[Proto Dumper] Generating minimal info for proto {proto_name}");
        }

        let mut message_info = MessageMinimalInfo::new(0);
        let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
            dump_message_info(
                i,
                proto_type,
                &proto_name,
                &dump_mode,
                &type_cache,
                enable_logging,
                &mut message_info,
            )
        }));

        match result {
            Ok(Ok(())) if message_info.fields.is_empty() => stats.empty += 1,
            Ok(Ok(())) => stats.ok += 1,
            Ok(Err(err)) => {
                stats.skipped += 1;
                log::warn!("[Proto Dumper] {proto_name} (typedef #{i}) skipped: {err}");
            }
            Err(payload) => {
                stats.panicked += 1;
                log::error!(
                    "[Proto Dumper] {proto_name} (typedef #{i}) panicked during field discovery, keeping {} partial field(s): {}",
                    message_info.fields.len(),
                    util::panic_message(&*payload)
                );
            }
        }

        minimal_info_map.insert(proto_type, message_info);
    }

    log::debug!(
        "[Proto Dumper] minimal info: messages={}, with_fields={}, without_fields={}, skipped={}, panicked={}",
        stats.total,
        stats.ok,
        stats.empty,
        stats.skipped,
        stats.panicked
    );
    if stats.total == 0 {
        anyhow::bail!(
            "no proto messages found in typedef range {proto_start}..{proto_end}; MergeFrom lookup failed for every type"
        );
    }
    if stats.skipped + stats.panicked > 0 {
        log::warn!(
            "[Proto Dumper] {} message(s) have incomplete field info, see the warnings above",
            stats.skipped + stats.panicked
        );
    }

    log::debug!("[Proto Dumper] generating nt...");

    let req_rvas = nt::get_req_map(&minimal_info_map, &rsp_notify_map, &mut req_map);
    let req_named_count = req_map.values().filter(|(_, name)| name.is_some()).count();
    log::debug!(
        "[Proto Dumper] req nt: req={}, nt={}",
        req_map.len(),
        req_named_count
    );

    let rsp_notify_names = nt::get_rsp_notify_names();
    let (method_handler_map, method_nt_map) = method_nt::get_method_nt_map();

    let (cmd_ids, proto_name_map, type_to_item) = output::generate_protobuf(
        &type_cache,
        &minimal_info_map,
        &rsp_notify_map,
        &req_map,
        &method_nt_map,
        &HashMap::new(),
        std::io::sink(),
    );

    let mut req_rsp_enum_nt = proto_name_map.clone();

    let cs_type_infos = {
        let mut result_map: HashMap<String, Vec<String>> = HashMap::new();
        let mut table_entries: Vec<(String, String, usize)> = Vec::new();

        for (rt, req_rvas) in &req_rvas {
            let valid_rvas: Vec<String> = req_rvas
                .iter()
                .filter(|rva| *rva != "0x0")
                .cloned()
                .collect();

            if valid_rvas.is_empty() {
                continue;
            }

            let formatted_name = rt.format_type_name(true);
            let obf_name = rt.il_name().into_owned();
            let deobf_name = proto_name_map
                .get(&formatted_name)
                .cloned()
                .unwrap_or_else(|| formatted_name.clone());
            result_map.insert(deobf_name.clone(), valid_rvas.clone());

            for rva_str in &valid_rvas {
                if let Ok(rva) = usize::from_str_radix(rva_str.trim_start_matches("0x"), 16) {
                    table_entries.push((obf_name.clone(), deobf_name.clone(), rva));
                }
            }
        }

        let _ = crate::proto::handler_nt::CS_HANDLER_TABLE.set(table_entries);

        result_map
    };

    let sc_packet_handlers = {
        let mut method_map: HashMap<RuntimeType, Vec<String>> = HashMap::new();
        let mut proto_param_map: HashMap<RuntimeType, Vec<String>> = HashMap::new();
        let rsp_notify_method_rvas = nt::get_rsp_notify_method_rvas();

        for i in 0..unsafe { il2cpp::MAX_TYPEDEFINDEX } {
            if let Ok(runtime_type) =
                RuntimeType::from_class(metadata_cache::get_typeinfo_from_typedefindex(i))
            {
                for method in runtime_type.get_methods_il2cpp() {
                    let args = method.get_parameters();
                    for arg in args {
                        if let Ok(arg_type) = arg.get_parameter_type()
                            && arg_type != runtime_type
                        {
                            let rva = method.get_il2cpp_method().rva();
                            if rva != 0 {
                                method_map
                                    .entry(arg_type)
                                    .or_default()
                                    .push(format!("0x{rva:X}"));

                                if let Ok(arg_name) = arg.get_name()
                                    && arg_name.as_str() == "proto"
                                {
                                    proto_param_map
                                        .entry(arg_type)
                                        .or_default()
                                        .push(format!("0x{rva:X}"));
                                }
                            }
                        }
                    }
                }
            }
        }

        let mut result_map: HashMap<String, Vec<String>> = HashMap::new();
        for rt in rsp_notify_map.keys() {
            if let Some(handlers) = method_map.get(rt) {
                let formatted_name = rt.format_type_name(true);
                let key = rsp_notify_names
                    .get(&formatted_name)
                    .cloned()
                    .unwrap_or_else(|| rt.il_name().into_owned());

                result_map.insert(key, handlers.clone());
            }
        }
        for (formatted_name, cmd_rvas) in rsp_notify_method_rvas {
            for cmd_rva in cmd_rvas {
                if cmd_rva != "0x0" {
                    let key = rsp_notify_names
                        .get(&formatted_name)
                        .cloned()
                        .unwrap_or(formatted_name.clone());

                    result_map.entry(key).or_default().push(cmd_rva);
                }
            }
        }

        for (rt, handlers) in proto_param_map {
            let il_name = rt.il_name();
            if il_name.len() == 11 && il_name.chars().all(|c| c.is_ascii_uppercase()) {
                let formatted_name = rt.format_type_name(true);
                let key = rsp_notify_names
                    .get(&formatted_name)
                    .cloned()
                    .unwrap_or_else(|| il_name.into_owned());

                result_map.entry(key).or_default().extend(handlers);
            }
        }

        for (key, handlers) in method_handler_map {
            result_map.entry(key).or_default().extend(handlers);
        }

        result_map
    };

    let mut proto_field_map = method_nt::dump_global_field_map();
    for (k, v) in handler_nt::get_handler_nt_map(&type_to_item) {
        proto_field_map.entry(k).or_insert(v);
    }

    let logic_field_map = proto_field_map.clone();

    logic_nt::run_logic_nt(
        &type_to_item.values().cloned().collect::<Vec<_>>(),
        &proto_name_map,
        &logic_field_map,
    );

    std::fs::write(
        "./DUMP/cs-type-infos.json",
        serde_json::to_string_pretty(&cs_type_infos)?,
    )
    .context("failed to write ./DUMP/cs-type-infos.json")?;

    std::fs::write(
        "./DUMP/sc-packet-handlers.json",
        serde_json::to_string_pretty(&sc_packet_handlers)?,
    )
    .context("failed to write ./DUMP/sc-packet-handlers.json")?;

    log::debug!("[Proto Dumper] generating protobuf...");

    let (cmd_ids_final, nt_map_final, type_to_item) = output::generate_protobuf(
        &type_cache,
        &minimal_info_map,
        &rsp_notify_map,
        &req_map,
        &method_nt_map,
        &proto_field_map,
        out,
    );

    for (obf_name, deobf_name) in nt_map_final {
        req_rsp_enum_nt
            .entry(obf_name)
            .or_insert_with(|| deobf_name);
    }

    writeln!(cmdid_out, "{}", serde_json::to_string_pretty(&cmd_ids)?)
        .context("failed to write packet ids")?;

    log::debug!(
        "[Proto Dumper] Protos dumped! messages={}, cmd_ids={}, rsp/notify={}, req={}",
        minimal_info_map.len(),
        cmd_ids.len(),
        rsp_notify_map.len(),
        req_map.len()
    );

    Ok(())
}
