# Event_Log：Isabelle/ML 侧的持久事件日志

**状态**：2026-08-30 终稿。初稿经两位评审两轮对抗评审，全部裁决（§2）已由作者定案。§10 第 1、2、3 步已实施并全部通过验证（2026-08-30：`Phi_System_Base` 与 `Phi_System` 整链在 `ML_debugger=true` 下构建通过；`Phi_Semantics_Framework` 构建期间三个类别写出首批真实记录——`guess_inst` 231 条、`guard_race` 111 条、`exception` 3 条 `Interrupt_Breakdown`（采集点 guard-racer R-conv，`size_heap`≈6.9GB/`time_GC`≈15s 同录），零坏记录；`Guard_Race_Smoke.thy` 全部探针对迁移后的 XML 读回逐字通过）；第 4 步经作者裁决跳过；第 5 步（探针删除）已完成；实施中被迫做出的修正已回写进本档（§2.4 建目录、§4 捕获器中断分支、§4 签名加 `log_dir` 与 `read_file`、§4 `record_breakdown` 助手、§5 边界变换改双射——2026-09-14 整个变换撤回，改为注释标记（§5 修订）、§5 抛出点位置键），各处均带「实施修正」标记。

## 0. 一句话

`Event_Log` 是整条 Isabelle/ML 依赖链（`Performant_Isabelle_ML` → `Auto_Sledgehammer` → Isa-Mini → phi-system）共用的**一支笔**：任何代码把一条带类别、带时间戳的记录追加到磁盘上的 XML 文件里，写入永远不抛错、永远不改变证明结果。异常报告只是其中一个类别（`Exception_Log`）。

## 1. 术语（全文只用这些名字）

| 术语 | 含义 |
|---|---|
| **记录**（record） | 一次 `append` 写出的一个 XML 顶层元素 `<record …>…</record>` |
| **记录属性** | `<record>` 元素自己的属性，由 `append` 统一填 |
| **类别**（category） | 记录的种类；一个类别**值**绑定一个 ML 类型和一个编码器；一个类别一个目录 |
| **编码器**（encoder） | `'a -> Properties.T * XML.body`，把记录的 ML 值变成属性与子元素；它就是该类别的 schema |
| **日志目录** | 所有类别目录的父目录；由环境变量 `ISABELLE_EVENT_LOG_DIR` 决定 |
| **采集点** | 用 `Exception_Log.capture` 包住的函数调用处：捕获异常 → 记帧列表 → 写记录 → 原样重抛。记录里的 `site` 属性就是采集点的名字 |
| **记录点** | 不取帧列表、直接 `append` 一条异常记录的调用处（中断类观测只能这样做） |
| **帧列表**（trace） | 异常展开时经过的函数帧，`(函数名, 函数定义处位置)` 列表，只含 `ML_debugger` 编译的帧 |

## 2. 定案的决策（2026-08-30，含两轮评审后的修订）

1. structure：**两个文件两个结构**。`library/event_log.ML` → `Event_Log`（通用：`category`/`append`/`comment`）；`library/exception_log.ML` → `Exception_Log`（异常类别、`capture`、帧列表压缩截断、`Par_Exn` 拆分、中断策略）。都放 `Performant_Isabelle_ML`，由 `Performant_Isabelle_ML.thy` 加载。
2. 配置：**单一环境变量 `ISABELLE_EVENT_LOG_DIR`**。未设 → 默认 `$ISABELLE_HOME_USER/event_log`（**默认开启**）；设为空串 → 关闭。不用系统选项（`Performant_Isabelle_ML` 不是注册组件，其 `etc/options` 不会被读，`options.scala:257` 只扫组件目录），不用 `declare` 属性（上下文级旋钮改不了进程级事实，且对无 context 的 `append` 无效）。想要 Isabelle 原生入口的用户在某个已注册组件的 `etc/settings` 里 export 它。
3. 频率责任交给类别：`exception` 类别默认开（单条 KB 量级、低频——`capture` 只在异常**逃出采集点**且过了 `record` 谓词时才写，被就地处理的异常零日志）；**高频类别各自带布尔开关、默认关**：新 Config `\<phi>log_guard_race`、`\<phi>log_guess_inst`（`Attrib.setup_config_bool`，默认 false，替代原路径配置），由调用点自查——这两处调用点都持有 ctxt，而 `category` 值里的 `enabled` 是进程级开关（无 ctxt 可用），上下文级开关属于调用点。不做轮转、不做清理。
4. 文件布局：`<日志目录>/<category>/<启动时间>-<pid>.xml`；**路径在每次写入时按 `ML_Pid.get ()` 求值**——记忆化的是 `(pid, 路径)` 对，pid 与记忆不符（本进程是继承堆的子会话）就以当前时间与当前 pid 重算，"启动时间"因此实为**本进程首次写入的时间**。这样做是因为会话堆镜像会把初始化期算好的路径连同持有它的 `Synchronized.var` 一起传给并行的子会话进程（`ml_heap.ML:35-36`）。目录由纯 ML 的递归 mkdir 保证存在（**实施修正**：原稿写 `Isabelle_System.make_directory`，但它走 Scala 桥，裸 ML 进程（如 `isabelle console`）没有 Scala——日志器不得依赖它；实测正是在裸进程里失效后改的）。文件无 `<?xml?>` 头、无根元素、无首行注释。
5. 格式：**XML，一条记录一个顶层元素，可跨多行**。记录边界是每个条目前的一行注释标记 `<!-- record -->`（§5；2026-09-14 修订——原文"由一次机械变换保证……是定理不是纪律"描述的是评审 agent 的补空格方案，已撤回）。不用 JSONL（Isabelle/ML 没有 JSON 编码器，Pure 只有 `json.scala`）；不用 MessagePack（中途损坏无法重同步；`mlmsgpack` 虽已在本 session 加载，此理由独立成立）；不用 YXML（Python 侧无解码器、不可 grep，而读取端就是 Python 和人）。
6. 现有探针：`\<phi>guard_race_log`、`\<phi>guess_inst_probe` 并入为类别 `guard_race`、`guess_inst`（路径配置删除、换成各自开关）；`guard_race` 的 `.goals` 伴生文件（`reasoners.ML:1466`，靠 serial 相连）**合并进同一条记录**、serial 列删除——多行内容在 TSV 里要外键另开文件，在 XML 记录里就是子元素，这正是迁移的收益样板。`breakdown_probe.ML` 与 `proof_store_probe.log` 两个临时探针：其调用点先改接 `Exception_Log`（见 §7 的记录点），**替换完成后**才删文件。
7. 帧列表**保留为第一等信息**（作者裁决：debug 就是为了定位问题；成本只在 `ML_debugger` 编译的代码上存在，见 §3）。采集点与记录点的完整清单在 §7，其中 `Phi_Reasoner.reason`/`reason1` **列入采集点**（作者裁决，成本分析见 §7）；Minilang 的 `timed_OPR` **不加**（作者裁决）。
8. `ML_debugger` 范围暂不扩大：现状只有 PLPR 开（`PLPR.thy:65`）。**待办（作者定开关形式）**：该 declare 目前是无条件的，任何源码构建都会 debug 编译 PLPR；要让"发行构建不开 debug"成真，需把它改为受开关控制。

## 3. 事实依据（两轮评审逐行核实后的版本）

- **帧列表只能来自调试器钩子。** Poly/ML 5.9.2 的 `PolyML.Exception.traceException` 是空实现（`basis/PolyMLException.sml:41`），所以 `ML_exception_trace` 选项无效。有效机制是 `Exn_Debugger.capture_exception_trace`（`Pure/ML/exn_debugger.ML`）。它在 Isabelle 里的**唯一**调用点是 `Runtime.exn_debugger`（`runtime.ML:167`），经 `Runtime.controlled_execution`（`runtime.ML:197-199`）包住**每条 Isar 命令事务**（`toplevel.ML:279/288/298/323`、`command.ML:305`）——但只在 `ML_exception_debugger` 打开时生效，且结果只打给 `tracing`。所以 `Exception_Log.capture` 的价值是：**把帧列表落盘成结构化记录，并且不要求使用者预开 `ML_exception_debugger`**。
- **钩子的成本结构。** `update_trace`（`exn_debugger.ML:23-26`）对激活区间内**每一次**异常穿过 debug 编译帧都无条件 cons 一条 `(帧, 异常值)`——不管该异常随后是否被就地处理；按异常身份的过滤（`eq_exn`，名字+位置）在区间结束时才做，正常返回则全表丢弃。因此代价 ∝ 区间内异常流量 × 穿过的 debug 帧数，且表项持有的异常值滞留到区间结束。不开 debug 的代码里不存在钩子调用点，代价严格为零。
- **`trace_var` 是单值线程局部**（`exn_debugger.ML:18-32`）：嵌套时内层 `stop_trace` 把它清成 `NONE`，外层从此记不到。⇒ 帧采集**每根线程只能有一层**，规则是"最外层记一次、内层直通"。这也意味着 `capture` 与 `ML_exception_debugger` 在同一线程互斥——`capture` 生效时，Isabelle 自己那层拿到空表。
- **中断族拿不到帧。** `capture_exception_trace` 第一步 `Exn.result`（`exn.ML:125-126`）对三种中断（裸 `Interrupt`、`Interrupt_Break`、`Interrupt_Breakdown`）直接重抛，取帧代码不执行。中断只能由**记录点**（无帧 `append`）观测。`Interrupt_Breakdown` 本就没有抛出点位置，帧对它也无从谈起；它的诊断价值就是"第一个看见它的站点"（`breakdown_probe.ML` 的立论）。
- **捕获器的选择只有一个是对的。** `Exn.result` 看不见中断；全局 `Exn.capture_body` 是托管中断版（`isabelle_thread.ML:163-164/194`）：`check_interrupt` 会消耗线程的 break 标志（`:149-150/154`），**捕获后丢弃结果**会吞掉用户取消、并让下一次真取消被判成 `Interrupt_Breakdown`（`:152`）——日志器制造它要诊断的故障（`race.ML:300-303` 的注释证明这本账被依赖）；`Isabelle_Thread.try_catch` 的中断分支写死重抛、不调 handler（`:183`）。**唯一对所有异常一视同仁、不碰账本的是 `Exn.capture0`**（`exn.ML:91`）。
- **抛出点位置永远可得**：`Exn_Properties.position` 不依赖调试器，`Exn.reraise` 保留它；帧列表为空时是兜底线索。但中途任何 `handle e => raise e`（非 `Exn.reraise`）会换掉位置并使 `eq_exn` 从那一点起静默截断帧列表（`PolyMLException.sml:51-54`）——这是使用条件，实施后在 phi-system grep 一遍。
- **XML 侧**：`XML.string_of` 是扁平序列化、从不产生换行（`xml.ML:150-163`）；文本与属性值必转义 `<`（`xml.ML:122/129/135`）但**不过滤控制字符**，而 PIDE 打印的项带 YXML 控制字节 `chr 5/6`（`xml0.ML:97-98`），是 XML 1.0 非法字符——两个现存探针都为此手工剥离过（`reasoners.ML:1456-1458`、`guess_instantiate.ML:217-221`）。`XML.parse` 认注释（`xml.ML:201-237`）、不认数字字符引用（`decode` 只有五个实体，`xml.ML:115-120`）、不做属性值换行归一化（而 Python 的 expat 做，`xml.ML:196-199` 对照）。
- **Isa-Mini 的 ML 侧没有日志系统**：AoA 的日志全由 Python 写（`model.py:12462`），ML 侧只把 `log_dir`/`invocation_id` 交给 RPC（`agent_server.ML:1752`）。`Event_Log` 是这条 ML 链上的第一个日志系统。

## 4. 接口

```sml
signature EVENT_LOG = sig
  type 'a category
  val category : {name: string, enabled: unit -> bool,
                  encode: 'a -> Properties.T * XML.body} -> 'a category
  val append   : 'a category -> 'a -> unit
  val comment  : 'a category -> string -> unit
  val log_dir  : unit -> Path.T option   (*NONE = 关闭*)
  val read_file : Path.T -> XML.tree list   (*ML 侧读回（§8），坏段丢弃*)
end
```

（**实施修正**：签名比原稿多了两个入口。`log_dir`——`Exception_Log.capture` 的快速路径要在日志关闭时直接调 `body ()`、连帧采集都不开，测试也要用它定位文件；暴露"日志目录或关闭"这个既有概念，不引入新概念。`read_file : Path.T -> XML.tree list`——§8 本就承诺 ML 侧读回，Guard_Race_Smoke 的迁移是第一个用户，逆变换逻辑只应存在一份。）

- `category` 是**纯值构造器**：不查表、不注册、不幂等。每个类别在拥有它的结构顶层 `val` 声明一次——重复注册在语言层面不存在，幻影类型参数 `'a` 永远诚实（评审阻断 8 的修法）。`enabled` 是该类别的**进程级**开关（`exception` 恒真）；上下文级开关（如 `\<phi>log_guard_race`）由持有 ctxt 的调用点自查后才 `append`，见 §2.3。
- `append`：日志目录为空或 `enabled ()` 为假时是 no-op。写入纪律见 §6。记录属性统一填：`category`、`ts`（ISO 8601 毫秒）、`theory`（从线程局部 `Context.get_generic_context ()` 取，`context.ML:102/708`，取不到则省略）、`Position.properties_of (Position.thread_data ())` 摊开的标准位置键（`line`/`file`/…，`markup.ML:435`）、`thread`（`Isabelle_Thread.print`）、`task`（`Future.worker_task` 及 group）。
- `comment`：把人写的固定文本以 `<!-- … -->` 追加到该类别文件，前面同样写一行边界标记（§5）；内容里的 `--` 被拆开；只用于人写的固定标记，程序生成的说明做成记录。
- 编码器辅助（普通函数，不是子结构）：标量字段直接进 `Properties.T`（无需组合子）；长内容三个助手——`elem_pretty : string -> Pretty.T -> XML.tree`、`elem_text : string -> string -> XML.tree`、`elem_list : string -> ('a -> XML.tree) -> 'a list -> XML.tree`。项只写可读打印（`Syntax.string_of_term` 过 `Protocol_Message.clean_output`，`protocol_message.ML:13/44`——不要重抄 `RPC_Pretty.trim_markup`，`Isabelle_RPC` 在上层够不着）；不写 `Term_XML`（计划稿写的 `Encode.term` 需要同 theory 的 `Consts.T` 才能解码，Python 侧无解码器；将来需要可回读的项时用 `term_raw` 另案）。**约束**：任何可能含换行的字段只准进子元素、不准进属性（`XML.parse` 与 expat 对属性值换行的处理不同，两侧读回会不一致）。

```sml
signature EXCEPTION_LOG = sig
  type report = {site: string, exn: exn, trace: (string * Position.T) list}
  val category : report Event_Log.category
  val default_record : exn -> bool   (*排除 proper 中断与 Timeout.TIMEOUT*)
  val capture : {site: string, record: exn -> bool} -> (unit -> 'a) -> 'a
end
```

- 帧列表由 `Exn_Properties.position_of_polyml_location`（`exn_properties.ML:30-35`）转换（`capture_exception_trace` 返回的是 `polyml_location`）。
- `record` 谓词是**参数**：`Success`、`Automation_Fail` 等控制流异常的名字在 PLPR，底层够不着；phi-system 的采集点自己叠 `fn e => default_record e andalso not (is_plpr_control_flow e)`。`Interrupt_Breakdown` 无视谓词恒记。
- 没有 `report` 函数：记录点直接写 `Event_Log.append Exception_Log.category {site, exn, trace = []}`。（**实施修正**：例外一个——`Exception_Log.record_breakdown : string -> exn -> unit`，"是或（经 `Par_Exn`）含 breakdown 才无帧记录"的助手。这一惯用法在 race.ML、sledgehammer_solver.ML、agent_server.ML 共出现八处，`Par_Exn` 包含性判断不应复制八份；普通记录点仍直接 `append`。）

`capture` 的实现（要点，完整论证见评审记录；与 `library/exception_log.ML` 一致）：

```sml
val tracing_here = Thread_Data.var () : unit Thread_Data.var;

fun capture {site, record} body =
  if is_some (Thread_Data.get tracing_here) orelse is_none (Event_Log.log_dir ())
  then body ()                                    (*内层直通 / 日志关闭：零成本*)
  else
    Thread_Attributes.uninterruptible_body (fn run =>
      (case Exn.capture_body (fn () =>
          Thread_Data.setmp tracing_here (SOME ())
            (fn () => Exn_Debugger.capture_exception_trace (run body)) ()) of
        Exn.Res (_, Exn.Res x) => x
      | Exn.Res (trace, Exn.Exn exn) =>
          ((if record exn then append {site, exn, trace = convert trace} else ());
           Exn.reraise exn)
      | Exn.Exn exn =>                            (*中断族从 capture_exception_trace 直接飞出*)
          ((if Exn.is_interrupt_breakdown exn
            then append {site = site, exn = exn, trace = []} else ());
           Exn.reraise exn)));
```

（**实施修正**：原稿的中断分支写的是 `Isabelle_Thread.check_interrupt exn0`，但 `check_interrupt` 不在 `ISABELLE_THREAD` 签名里、够不着。可达的逐字等价物是最外层的全局 `Exn.capture_body`——它就是 `Isabelle_Thread.Exn.capture_body`，对 raw 中断调一次 `check_interrupt` 归一（break 标志恰好消耗一次）——**加上恒重抛**。§3 禁的是"捕获后丢弃"；捕获后恒重抛与 `Isabelle_Thread.try_catch` 中断分支的 `Exn.reraise (check_interrupt exn)` 语义一致。普通异常不会走到最外层的 `Exn.Exn` 分支：`capture_exception_trace` 内部的 `Exn.result` 已把它们装进返回值。）

三种情况的行为：普通异常——记帧、原样重抛，break 标志不动；proper 中断——不记（谓词），归一后重抛，取消照常生效（与 Isabelle 在 Isar 命令边界 `runtime.ML:202` 的动作逐字一致，账本只消耗一次）；`Interrupt_Breakdown`——无帧记录"第一个看见它的采集点"。`body` 经 `run` 拿回调用者原本的中断属性，所以被包函数的可中断性不变，`race.ML:62-71` 的调用方义务 (b)（race 不得在中断已延迟时被调）不受影响——这条是三条不变式里唯一靠论证不靠类型的，实施后要实测确认。`tracing_here` 标记只属于**帧采集**：记录点和无帧写入不置它，不会挡住内层的帧采集。

## 5. 文件与记录格式

一条记录 = 一个 `<record>` 元素，由 `XML.string_of` 输出；每个条目（记录或人写的注释）前先写一行边界标记 `<!-- record -->`，条目后补 `"\n"`。标记不可能出现在条目内部：文本与属性值里的 `<` 必被转义（`xml.ML:122`），注释体里的 `--` 被写端拆成 `"- -"`（注释非法串在语言层面写不出来），而标记含 `--`。读取方按标记切段即可，不需要任何字符变换。`append` 过滤 `\t\n\r` 之外的控制字符；编码器内的 `clean_output` 是第一道。

（**修订 2026-09-14** [作者 "标记文本就用 `<!-- record -->`"]：原先的边界是一次字符变换——对"换行 + 空格* + `<`"的行补一个空格，使"除首行外没有任何一行以 `<` 开头"成为定理，读端再删一个空格还原。那是评审 agent 的方案，作者 2026-08-30 批准的设计里没有它，作者认为它"太黑"，改为明面上的注释标记。旧格式的日志文件由 `ai-artifacts/event_log_migrate.py` 一次性迁移；该脚本已完成使命，2026-09-23 起不再跟踪（作者裁定实验脚本不提交），可在提交 `a28e6f2` 读到。）

```
<!-- record -->
<record category="exception" ts="2026-08-30T17:02:11.123" theory="Phi_Examples.Bucket_Hash"
 line="191" file="…" thread="worker 7" task="…"
 site="guard-racer P-auto" exn="ERROR" raised_line="…" raised_file="…"
 size_stacks="…" size_heap="…" time_GC="…"><message>…Runtime.exn_message，截断 16 KiB…</message>
 <trace total="187391" compressed="14" written="14"><frame fn="Merely_Rewrite.go'" file="…" line="…" repeat="187342"/>…</trace></record>
```

（`XML.string_of` 本身不产生换行，换行只来自编码器的 `Text` 内容；示例为了可读手工折了行，仅示意字段。）标量一律进属性，`message`/`trace`/`goal` 等长内容进子元素；`Par_Exn` 容器拆开逐个 `<exn …/>`。抛出点位置是 `Position.properties_of` 的标准键机械加 `raised_` 前缀（**实施修正**：原稿只列 `raised_line`/`raised_file`，但 PIDE 编译的代码位置是 offset 制、没有行号，实测 `raised_line` 拿不到而 `raised_offset` 有——机械前缀两种环境都覆盖）。注意：`Interrupt_Breakdown` 与 proper 中断的记录**没有 `<trace>` 子元素**（§3：中断族拿不到帧），它们的信息就是记录属性 + `<message>`。

帧列表处理（先压缩后截断）：列表从最内层到最外层，每条是 `(函数名, 函数定义处位置)`——位置是定义处而非调用点，这正是压缩规则安全的原因。(1) 相邻相同的 `(函数名, 位置)` 合并加 `repeat`（深递归从几十万条变一条，`repeat` 即诊断结论；交替递归不合并）；(2) 压缩后仍超 300 条时保留最内 200 + 最外 100，中间 `<elided frames="N"/>`；(3) `<trace total= compressed= written=>` 让截断可见，旁注"帧列表止于最近一次用 `raise`（非 `Exn.reraise`）改变位置的重抛"。三个常数是 `Exception_Log` 内部常量。

## 6. 写入纪律

- 不持有流：每条记录一次 `File.append`（`file.ML:136`，即三个现存探针的做法；`File_Stream` 本就是 BinIO）。每类别一个 `Synchronized.var`，既当进程内互斥锁、又装 §2.4 的 `(pid, 路径)` 记忆——一个变量两个职责，写入在锁内完成。
- 整个写入路径（拼串 + `File.append`）放在 `Thread_Attributes.uninterruptible_body` 里，用 **`Exn.capture0`** 捕获：非中断异常丢弃（首次失败 `Output.warning` 一次），中断 `Exn.reraise`。**禁止**用全局 `Exn.capture_body` 吞异常（评审阻断 3）。
- 消息截断 16 KiB；帧列表按 §5。

## 7. 采集点与记录点（定案清单）

**采集点（`capture`，带帧列表）：**

| 位置 | 覆盖 | 激活区间上界 | 备注 |
|---|---|---|---|
| `Phi_Reasoner.reason`/`reason1`（`reasoner.ML:934/940`） | φ-LPR 推理核心的一切失败 | 无界 | **作者裁决列入**：这是整个推理的核心，不包则异常捕获形同虚设；成本只在 `ML_debugger` 编译时存在（PLPR 的 `Success` 控制流会在激活区间内持续 cons 并滞留 `(ctxt, thm)`，量级未测），debug 本就是定位问题时才开的。递归嵌套由"最外层记一次"自然处理。§10 的整跑要量堆峰值，作为数据而非门槛 |
| guard race 的 racer 体（`reasoners.ML:1370-1392`） | racer 崩溃 | `\<phi>guard_race_timeout` 5s | worker 线程，与命令线程的采集互不干扰 |
| hammer 入口（`Phi_Sledgehammer_Solver` 分支体） | sledgehammer 一路 | hammer 超时 | worker 线程 |
| store 回放（`proof_store_AoA.ML` 的 `replay`） | 回放失败 | `tolerant_time` 预算 | 取代临时探针的主要用途 |
| `\<phi>type_def` 派生义务求解（`deriver_framework.ML`） | 派生器义务失败 | 单义务时长 | |

**记录点（直接 `append`，无帧）：**

| 位置 | 覆盖 |
|---|---|
| `race.ML:203-204` 与 `:270`（中断逃出比赛的两个分支） | 中断/Breakdown 归因——今天 `breakdown_probe` 的全部价值；先接上这两处才许删探针 |
| `reasoners.ML:1326-1332` 的 `checked_io` | 诊断 I/O 自身的失败 |
| 最外层 `\<phi>` Isar 命令实现 | 兜底：漏网异常的无帧记录（有帧版留作 §10 的实验项） |

**明确不加**：Minilang 的 `timed_OPR`（作者裁决）；Isa-Mini 其余入口（`hammer_or_aoa_method`、`run_AoA`，另案，记录带 `invocation_id`）。

**探针迁移**：`guard_race`（含 `.goals` 合并）、`guess_inst` 两类别在 `reasoners.ML`/`guess_instantiate.ML` 顶层声明；记录属性与 `<stats>` 的取值代码从 `breakdown_probe.ML:33-54` 搬（`ML_Statistics.get`/`Isabelle_Thread.print`/`Future.worker_task`+`Task_Queue.str_of_task_groups` 逐项就是所需），不照描述重写。

## 8. 读取

按边界标记 `<!-- record -->` 切段，逐段 `xml.etree.ElementTree.fromstring`，坏段跳过，注释跳过；标量都在属性里，`pandas.DataFrame(r.attrib for r in records(path))` 即成表。参考实现 `Performant_Isabelle_ML/tools/event_log.py`（`records`/`chunks`/命令行 TSV 三个入口）。Isabelle/ML 侧读回：同样切分 + `XML.parse`（格式内无数字字符引用，两侧对称）。

## 9. 明确不做的

- 不在 Python 侧改 AoA 的日志。
- 不接管 `setOnExitException` 钩子。注意 `capture` 生效的线程上 `ML_exception_debugger` 拿到空表（§3 单值 `trace_var`）——这是共存代价，写在此处而非隐瞒。
- 不引入 XSD/DTD；schema 就是编码器代码。
- 不做轮转、清理、字节上限（被评审否决为脏 hack）；体积责任在类别开关。

## 10. 实施顺序

1. `Performant_Isabelle_ML`：`library/event_log.ML`、`library/exception_log.ML`、`Performant_Isabelle_ML.thy` 加载、`tools/event_log.py`。
2. 单元测试 theory（`Test/`）：三条记录、一条注释、一条人为坏记录、一条带控制字符与换行的项打印，Python 读回验证"坏一条丢一条"与内容逐字往返。
3. phi-system：两个探针迁移（§7）；记录点接入；采集点接入（racer → store 回放 → deriver → hammer → `reason`，由小到大）。
4. ~~`Phi_Examples` 整跑 ×2（接入前后）：比总耗时与堆峰值~~ **作者裁决（2026-08-30）：跳过此步**；最外层 Isar 命令的有帧版实验随之搁置（留在 §7 备注里）。
5. 替换完成后删除 `breakdown_probe.ML` 与 `proof_store_probe.log` 探针、`PLPR.thy:1958/1970` 的两条临时 declare。**已完成（2026-08-30）**：删除了 `breakdown_probe.ML` 及其装载行、两条 declare（`guard_race`/`guess_inst` 自此回到默认关），以及 `proof_store_probe.log` 的全部八处写入（`proof_store_AoA.ML` 的 REPLAY_EXN 与 GOAL/HIT/MISS/REPLAY_FAILED、`agent.ML` 的 INTRO_UNMATCHED、`agent_server.ML` 的 REPLAY_STEP_FAILED 与 REPLAY_EXN_DETAIL、`cache_file.ML` 的 KEY_COLLISION 与 MISS/HIT/REPLAY_TIMEOUT/REPLAY_FAILED、`deriver_framework.ML` 的 OBLG_SIMP_TIMEOUT）。按 §2.6 的"调用点改接"，八处 `Breakdown_Probe.log` 调用点作为 `record_breakdown` 记录点**保留**（无 breakdown 时零开销）。
6. 另案：Isa-Mini 接入；`PLPR.thy:65` 的 `ML_debugger` declare 改为受开关控制（§2.8 待办）；可回读项编码（`term_raw`）。
