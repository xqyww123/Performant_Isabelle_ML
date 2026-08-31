# `Interrupt_Breakdown` 治理方案(rev 2,2026-08-31)

**状态:rev 2 已按四视角对抗评审(§8)逐条修订,含作者对 R1/R2/R3 与三项裁决的决定;
待作者通读批准。未实施。**

**范围**:`contrib/Performant_Isabelle_ML` 及其下游(`auto_sledgehammer`、`Isa-Mini`、
`phi-system`、`Isa-REPL`、`Isabelle_RPC`)。**硬约束:不修改 Isabelle 发行版(Pure/HOL)的
任何文件**;治本的发行版修复走上游报告(§4.6)。已知同类隐患存在于 `Semantic_Embedding`
(见 §5),不在本方案范围。

---

## 1. 术语表(本文一律使用下列全称)

| 术语 | 含义 |
|---|---|
| **break 账本** | Isabelle 给每个线程配的布尔字段 `break`(`Pure/Concurrent/isabelle_thread.ML:45`):自家发中断前置真,接住裸中断时读并清——真判 `Exn.Interrupt_Break`,假判 `Exn.Interrupt_Breakdown` |
| **裸中断** | Poly/ML 的 `Thread.Thread.Interrupt`,`Exn.is_interrupt_raw` 认的那个;**尚未审判**的中断 |
| **proper 中断** | `Exn.is_interrupt_proper` = 裸中断 ∨ `Interrupt_Break`(`exn.ML:116`),即"尚未审判,或已判为自家取消"——裸中断是**乐观归类**进来的,proper 不等于已验证 |
| **中断族** | `Exn.is_interrupt` = proper 中断 ∨ `Interrupt_Breakdown`(`exn.ML:117`) |
| **探测—清账缝** | `expose_interrupt_result`(`isabelle_thread.ML:167-176`)里探测(`:172`)与清账(`:175`)两步之间的非原子区间 |
| **带账超时包装** | §4.2 的机制:包住 `Timeout.apply`,以包装自己的计时器请求为见证,把"本层计时器已开火后落地的 Breakdown"改判为 `Timeout.TIMEOUT` |
| **包装自己的计时器请求** | 带账超时包装在调用 `Timeout.apply` 之前向 `Event_Timer` 登记的、回调体为空、不发任何中断的请求;`not (Event_Timer.cancel req)` 即"本层计时器已开火"这一事实 |
| **中断族判据内核** | 从 `race.ML` 的 `contains_interrupt` 提取到共享位置的逐分量判据(§4.2),能看穿 `Par_Exn` 容器 |

## 2. 机制(已证实;完整证据链见 2026-08-30 的源码求证报告)

**缺陷不变式**:break 账本记录的是"本线程有一次未消费的正规取消"这一**布尔**事实——不计数、
不记来源;消费它的动作与产生它的动作之间**没有原子性保证**。两条产地:

**(甲)探测—清账缝。** `expose_interrupt_result` 先做一次不加锁的快速探测(`:172`,读
`requestCopy`,读到 0 直接返回),再**无条件**清账(`:175`),且 `test` 不是中断时把读到的账
直接丢弃(`:176`)。一次外来取消(`interrupt_thread` 先挂 Poly/ML 请求、后置账,`:145-147`)
若落在这两步之间:请求探测不到(探测早于请求诞生),账却被读走丢弃。此后裸中断落地,查账
为空 → `Interrupt_Breakdown`。九步最短交错见求证报告 §5.2。放大器:Future 调度器**每 50 毫秒**
(`future.ML:161`,`next_round = seconds 0.05`)对未死透的已取消组重发一遍取消
(`future.ML:337-343`),线程退出路径上密集经过 `Timeout.apply` 收尾(`timeout.ML:49` 每次
都过这条缝)。缝的宿主共四处:`timeout.ML:49`、`future.ML:217`(`interruptible_task` 收尾)、
`future.ML:237`(`worker_exec` 的 finish 段)、`command.ML:228`。

**(乙)布尔折叠。** 精确时序:第一次投递已被 Poly/ML 取走(`processes.cpp` 清 `requests` 与
`requestCopy` 后抛异常),但 `check_interrupt` 的 `reset_interrupt`(`isabelle_thread.ML:149-150,
154-155`)尚未执行;第二次 `interrupt_thread` 恰挤进这个窗口,重新挂请求位并把已为真的账再置
一次真(布尔无从计数,`:152`);随后第一次中断的 `reset_interrupt` 读走并清掉这唯一的一笔;
第二次投递落地时查账为空 → `Interrupt_Breakdown`。

**已证伪的旧假设**:"`bash_process` 推迟投递期间探测漏掉 pending 请求"不成立——Poly/ML 侧
请求一旦挂上,同步探测必然取到(`processes.cpp:1685-1712` 只看中断位)。

**外泄案例的完整解释**(`Bucket_Hash.thy:191`,proof-store 回放):外层回放预算的计时器
(≈1.6 s,预算本身失真是另案,见 §5)到期时恰落进某个内层 `Timeout.apply` 收尾的探测—清账缝,
预算的账被内层吃掉;Breakdown 稍后落地,而 `timeout.ML:50-52` 的 `was_interrupt` 只认 proper,
**不转 `TIMEOUT`**,于是裸奔到命令层。内层 `Timeout` 自己的计时器与自己的缝互斥
(`Event_Timer` 的锁序),只有**外来**计时器/取消者能落进缝——这个非对称性精确解释了
"18 条实测记录全部落在刚被取消的组、唯一外泄走回放路径"的分布。

**定性(2026-08-30 作者质询后重读一手源码)**:"外来取消恰逢自己 deadline 被吞成超时"须按
取消的触发方式二分。Pure 的 Future 组取消这一路是**状态式**的(`cancel_group` 置持久状态,
`future.ML:399-400`;调度器每 50 毫秒重发脉冲),吞掉一个脉冲无损失,`Timeout.apply` 的认领
启发式在这条路上是设计自洽的;但 Pure 内部并非只有状态式——`Timeout.apply` 自己的计时器就是
**单发**的(`timeout.ML:41-43`),单发脉冲丢账即不可恢复。真正的缺陷在两个背离状态式纪律之处:
(1) 探测—清账缝使单发脉冲丢账变成 Breakdown;(2) `Timeout.apply` 收尾对 Breakdown 失明,使该
丢失不可恢复。本方案的 §4.2 补 (2),从而 (1) 的错标可凭本层计时器的事实恢复。

**同源异症,不在本方案范围,归 §4.6 的上游报告**:外来取消落在任务边界排干之后会以 proper
面目误杀下一个无辜任务;嵌套 `worker_exec` 的排干会把外层取消蒸发;`Timeout.apply` 收尾先
`release test` 再 `release result`(`timeout.ML:56`),收尾探测自造的 Breakdown 会顶掉身体真正
抛出的异常。

## 3. 已否决的方案(勿重提;完整论证见对抗评审报告)

1. **治愈边界**(把"组已取消"时的 Breakdown 改判回 `Interrupt_Break`):判据在非 worker 线程
   (Isa-REPL 命令线程,`Future.worker_group()` 返回 `NONE`)上不可用,唯一外泄案例恰在射程外;
   "组已取消"沿祖先链几乎恒真,无区分力;会把真实栈/堆耗尽静默改判成取消(OOM 时
   `future.ML:359-370` 靠 Breakdown 熔断调度器,改判等于拆保险丝);`Par_Exn` 容器内改判要么破坏
   其不变式(`par_exn.ML:23-24`)、要么把同容器里别的任务的真异常放出来。
2. **在用户空间复刻 `Timeout.apply` 的中断投递与线程属性切换**:被 §4.2 以更小的代价达成;复刻
   要承担 `Event_Timer` 回调锁序、属性 dance 出错反而制造真正来路不明中断等风险。**注意本条的
   边界已按 R1 收窄**:允许登记一个回调体为空、不发中断的计时器请求(见 §4.2),那不是复刻。
3. **竞赛不取消、让输家跑完**:guard race 上赢家中位 80 ms(`reasoners.ML:1049`)对输家预算
   `(1+n)×5000 ms`(`reasoners.ML:1287-1288`),两个数量级的 CPU 膨胀,不可行。
4. **协作式预算**(回放循环步间轮询 deadline、不发中断)——作者于 2026-08-30 否决,理由是对
   系统的修改面不可接受。防线由 §4.2 独立承担。
5. **挂钟 deadline 判据**(rev 1 的 §4.2 原形:`Time.now () >= start + scale_time t`)——评审
   证明它在三处与 `Timeout.apply` 内部不一致且方向都是激进的:非 physical 计时器按垃圾回收时长
   顺延到期(`event_timer.ML:79-82`),挂钟先于真计时器认为已到期,窗口宽度 = GC 时长,堆压力
   越大越宽;`Timeout.ignored`(<1 ms 纯透传、不装计时器,`timeout.ML:26,34`)未镜像;
   `timeout_scale` 与 `start` 被包装与被包装者各取一次。已由 R1 取代。
6. **健康判据**(rev 1 的 §4.4:读 `ML_Statistics` 与 Poly/ML stderr,报警时禁止改判)——作者
   于 2026-08-31 删除。理由:采纳 R1 后它的用处大幅缩小(计时器开火前的资源故障在形状上不可能
   被改判);评审评其为方案里形状最差的一处(全局、跨线程、带未定义时间窗的可变标志,让同一
   异常在不同时刻得到不同判决);且 `size_stacks` 是进程级聚合,测不到单线程栈耗尽,即测不到
   自己的头号目标。残余见 §7。

## 4. 方案(按落地顺序)

### 4.1 拆掉既有的无条件散点补丁

`Isa-Mini/library/proof.ML:1806-1809`、`:1811-1814`、`Isa-Mini/Agent/preprocess.ML:84-87` 三处
在 `Timeout.apply` 表达式**之后**挂着 `| Exn.Interrupt_Breakdown => …` 分支,把 Breakdown
无条件吞成 "Timeout"/`NONE`,连计时器开没开火都不查——OOM 与栈耗尽一并被吃。

**为什么先拆**:§4.2 的包装是就地替换 `Timeout.apply` 调用,因此落在这三处 `handle` 的**里面**;
handler 在外,会把包装刻意上抛的、计时器未开火时落地的 Breakdown 继续无条件吃掉,§4.2 想恢复
的可见性就白做了。§4.2 接管的是这三处行为的真子集——只有本层计时器已开火的那一类会被改判成
`Timeout.TIMEOUT`;未开火时产生的 Breakdown 从此原样上抛到 Minilang 命令层。这三处原本就漏掉
`Par_Exn` 容器内的 Breakdown(`par_exn.ML:26-33`),所以"今天全被吞掉"本身也只部分成立。

**作者裁决(2026-08-31)**:落到 Minilang 命令层的裸 Breakdown **当作错误上报**,不当作"这一步
被取消"——分不清"我们要的停"与"运行时崩了"时一律按后者上报。实现上这意味着**什么都不加**:
拆掉分支后不补任何把 Breakdown 转成 `OPR_FAIL`/`NONE` 的 handler,让它作为异常自然上抛,由
命令层按普通错误报告。

### 4.2 带账超时包装

**形状(作者裁决:R1、R2 均采纳,2026-08-31)。** `Performant_Isabelle_ML` 新增
`library/accounted_timeout.ML`,在 `Performant_Isabelle_ML.thy` 的 `ML_file` 序列中**尽早**加载
(须在 `race.ML` 之前,因 `race.ML` 将使用中断族判据内核),内含:

1. **中断族判据内核**:把 `race.ML:182-186` 的 `contains_interrupt` 提取到此处;`race.ML` 改为
   调用它并删去 `:180-181` 的 "interim home" 注释;`sledgehammer_solver.ML:567-572` 的
   "keep it in sync with that kernel" 待办顺手收敛。**不动** `joins_norm` 的递归 `flatten`
   (`sledgehammer_solver.ML:1853-1861`),它的递归性是有意的。另提供
   `all_breakdown : exn -> bool`:异常本身是 Breakdown,**或** `Par_Exn.dest` 得到的列表**非空**
   且每一个分量都是 Breakdown。"非空"必须写进实现:proper 中断的 `dest` 是 `SOME []`
   (`par_exn.ML:36`),否则会落进空真被改判。
2. **`Accounted_Timeout`** 结构:`raw_apply`/`raw_apply_physical`(原版逃生名,显式、可 grep)
   与带账的 `apply`/`apply_physical`,签名逐字对齐 `timeout.ML:16-17` 的
   `Time.time -> ('a -> 'b) -> 'a -> 'b`(`RPC.ML:373` 是偏应用形态,只有签名一致才能原地替换)。
3. **结构遮蔽**(R2):`structure Timeout = struct open Timeout; val apply = Accounted_Timeout.apply;
   val apply_physical = Accounted_Timeout.apply_physical end`,声明在文件**末尾**、
   `Accounted_Timeout` **之后**(它的 `raw_apply`/`raw_apply_physical` 在遮蔽之前绑定原版),
   且必须是文件顶层声明(进入 theory 的 ML 环境才能传给下游)。此后凡在 `Performant_Isabelle_ML`
   之下编译的 ML,写 `Timeout.apply` 拿到的就是带账版本——这是 Isabelle 自己的手法
   (`isabelle_thread.ML:194` 的 `structure Exn = Isabelle_Thread.Exn`)。`Timeout` 的签名
   (`timeout.ML:9-19`)**不导出** `apply'`,故 `open` 不会带入原版内部实现,无需另遮蔽(已核对)。

**骨架**(`raw` 是遮蔽前绑定的原版:`physical` 为真时是 `Timeout.apply_physical`,否则
`Timeout.apply`;`Exn.capture0` 是 `Isabelle_Thread.Exn` 里 `open Exn` 带来的、不经
`check_interrupt` 的裸捕获):

```sml
fun apply' physical t f x =
  if Timeout.ignored t then raw physical t f x      (*镜像 timeout.ML:34:无计时器、无记账、无改判*)
  else
    Thread_Attributes.uninterruptible_body (fn run =>
      let
        val start = Time.now ()
        (*包装自己的计时器请求:与 Timeout.apply 同一 physical 标志、同一到期算式
          (timeout.ML:42),回调体为空,不发任何中断,不取任何我们自己的锁*)
        val req = Event_Timer.request {physical = physical} (start + Timeout.scale_time t) (fn () => ())
        (*capture0,不是 capture:后者经 check_interrupt 消费 break 账本,等于自造本方案要治的病;
          身体经 run 在调用者原属性下跑,捕获、判定、抛出全在延迟中断的区间内*)
        val result = Exn.capture0 (fn () => run (raw physical t f) x) ()
        (*所有出口恰好 cancel 一次并把结果存下:第二次 cancel 会因"找不到"返回假,被误读成已开火*)
        val fired = not (Event_Timer.cancel req)
      in
        case result of
          Exn.Res y => y
        | Exn.Exn exn =>
            if fired andalso all_breakdown exn
            then raise Timeout.TIMEOUT (Time.now () - start)
            else Exn.reraise exn
      end)
```

**三条实现纪律(必须写进代码注释,先例 `race.ML:246-248`、`event_log.ML:162-163`)**:
(a) 用 `uninterruptible_body` + `Exn.capture0`——裸 `handle` 跑在调用者的可中断属性下,属性恢复
自带一次 `testInterrupt`(`thread_attributes.ML:57-58`)会顶掉在飞的异常;(b) **不得**用
`\<^try>… catch …`——`Isabelle_Thread.try_catch`(`isabelle_thread.ML:180-183`)在进入用户
handler 之前就把整个中断族(含 Breakdown)重抛掉,改判永不生效且静默;(c) 请求在所有出口恰好
`cancel` 一次。

**为什么这个判据是事实而不是启发式**:`not (Event_Timer.cancel req)` 与 `Timeout.apply` 自己判
`was_timeout`(`timeout.ML:48`)用的是**同一个动作、同一份虚拟时钟、同一把 `Event_Timer.state` 锁**
(`event_timer.ML:109,158-171`);垃圾回收顺延由 `event_timer.ML:79-82` 按同一套公式算,不由
我们承担。由此:GC 顺延偏差归零;`Timeout.ignored` 分支不登记请求,改判在形状上不可能发生;嵌套
时只有"自己的计时器真开火了"的那一层会认领,归属自动回到 §2 认定的正主。计时器开火**之前**
落地的 Breakdown(含真实的资源故障)一律原样上抛。

**遮蔽的前置实验**:落地前先做一次最小实验确认 ML 名字空间的合并确实把遮蔽传到了下游
(`Performant_Isabelle_ML/HOL/SSymb.thy` 把 `Main` 放在导入列表第一位,是已知的合并顺序敏感点);
实验失败则退回逐点改名 `Accounted_Timeout.apply` 加 CI 检查。依赖链已核实:
`Performant_Isabelle_ML/ROOT:1` 是 `session Performant_Isabelle_ML = Pure +`;
`auto_sledgehammer/Auto_Sledgehammer.thy:2` 导入 `Performant_Isabelle_HOL.SSymb`;`Isa-Mini/ROOT`
是 `session Minilang = Auto_Sledgehammer +`;`Isabelle_RPC/Remote_Procedure_Calling.thy:2` 与
`Isa-REPL/Isa_REPL.thy:2` 亦在下游。

**遮蔽的代价(作者已认)**:调用点上"我用的是哪个 Timeout"的显式性消失,补偿是模块头醒目注释
加 README 一行;遮蔽覆盖在 `Performant_Isabelle_ML` 之后加载的一切 ML,包括发行版 theory 在
我们会话里动态加载的 ML——这不改发行版文件,作者裁决其落在硬约束允许范围内。

**与 `Race` 引擎的叠加(同一提交落地)**:`Race` 的退出分类以 `Timeout.TIMEOUT` 为判据
(串行 `race.ML:208`、并行 `:254`),两处都排在中断归因(`:255-280`)之前;racer 体内的预算就是
`reasoners.ML:1416` 的 `Timeout.apply budget body ()`。遮蔽生效后,本 racer 自己的计时器开火之后
落地的 Breakdown 形态取消会被记为 `Timed_Out` 而非 `Cancelled`,调用者的取消在该情形下静默丢失。
量级很窄:guard race 上赢家中位 80 ms 认领,此刻输家的 5000 ms 计时器远未开火,退出仍是
`Cancelled`;只有落进探测—清账缝的那部分取消受影响。**`race.ML` 文件头残余 (b) 的改述必须与
遮蔽生效同一提交落地**:触发条件从"proper 中断恰在 deadline 到期那一瞬到达"放宽为
"Breakdown 形态的取消在本 racer 自己的计时器开火之后到达",并注明 `:208,254` 的 `Timed_Out`
分支排在归因之前是这条残余的实现原因。

**调用点**:遮蔽后无需改名。实施时仍以
`grep -rn "Timeout\.apply" contrib/{Performant_Isabelle_ML,auto_sledgehammer,Isa-Mini,phi-system,Isa-REPL,Isabelle_RPC} --include='*.ML' --include='*.thy'`
(zsh 下 `--include` 必须加引号)枚举一遍,目的只是核对:没有站点在遮蔽生效之前加载
(即不经 `Performant_Isabelle_ML` 的代码),也没有站点以 `raw_apply` 之外的方式拿到原版。评审时点实测约 39 处(含 `.thy` 三处、
`REPL.ML:949` 唯一的 `apply_physical`;已剔除注释与未加载的 `agent.old.ML`)。

**残余缺口**(如实记录,不承诺解决):(i) Breakdown 若在 `Timeout.apply` 返回**之后**才落地
(裸中断落点在下一个可中断点,已出包装的动态范围),包装够不着;(ii) 内外层计时器**都**开火时,
内层认领并可能被自己的良性 `handle Timeout.TIMEOUT` 吞掉,外层的一次性请求已被消耗,外层预算
静默失效——这是 `Timeout.apply` 既有语义(`timeout.ML:54` 同样接受"计时器开火但身体正常返回
则不报超时"),不为它引入线程局部帧栈;(iii) 属性恢复处的 `testInterrupt` 会顶掉在飞的异常,
`Timeout.apply` 自身同样存在,包装做不到比它更强;(iv) 计时器开火**之后**落地的真实资源故障
(如 `merely_rewrite.ML:662-667` 记录的发散重写导致的栈耗尽,按定义发生在长时间运行之后)仍会
被记为 `TIMEOUT`——**已知且被作者接受的残余**,由 §4.6 处理;(v) 包装的 `start` 取在进入
`Timeout.apply` 之前,比 `timeout.ML:39` 的 `start` 早微秒级,故包装自己的计时器请求比
`Timeout.apply` 的请求早微秒级开火——落进这几微秒的 Breakdown 会被认领而 `Timeout.apply` 自己
尚未开火;量级可忽略,如实记下。

### 4.3 (已删除)

rev 1 此处是"协作式预算",作者否决,见 §3 第 4 条。

### 4.4 (已删除)

rev 1 此处是"健康判据",作者于 2026-08-31 删除,见 §3 第 6 条;残余记入 §7。

### 4.5 (已删除)

rev 1 此处有两条:(一)`agent_server.ML:1919`、`:2135` 的 `Exn.capture Future.join` 后丢弃——
评审证明它**不是** Breakdown 产地也不是泄漏点(叶子作业、无人 join、异常只取消自己新开的
子组、组状态向上继承不向下汇总、收尾无条件排干);真实缺陷是掩盖 proof-store 写失败,与本方案
无关,挂号 §5。(二)进程级 `Lazy.lazy` 被 Breakdown 永久毒化(`lazy.ML:108` 只对 proper 中断
重置)——两处体内均无探测—清账缝宿主,只能作为别处丢账中断的落地点,从未观测到;作者于
2026-08-31 判定无需处理。

### 4.6 上游报告(治本)

报告内容:§2 的九步交错;"探测与清账不原子 + 账本不计数不记来源"的不变式缺陷;
`is_interrupt_proper` 与中断族之差在 Pure 里至少三处结构性地漏掉 Breakdown——`timeout.ML:50-52`
不认领超时、`par_exn.ML:23-24,27` 不当中性元过滤、`lazy.ML:108` 永久记忆;两条同源异症(任务
边界误杀、嵌套排干蒸发外层取消)与 `timeout.ML:56` 的顶替。修法在上游是现成的:探测与清账合成
一次持 break 锁的原子操作,或仅在探测确实取到中断时清账。

**呈述框架**按 §2 的二分法:Pure 的 Future 组取消是状态式的、自洽;缺陷只在单发脉冲的两处
背离。**提交纪律**:凡引发行版行号,一律注明所依据的发行版为 Isabelle2025-2,并在提交前逐条
复核;仓库内文件的行号不进上游报告。`async_manager_legacy` 在 `src/HOL/Tools/Sledgehammer/`,
是 HOL 层遗留,不能拿来当"Pure 内存在单发用法"的例证。报告成稿后由作者过目、决定署名与渠道。

## 5. 与相邻问题的边界(挂号,均为另案)

- **proof-store 记录的回放时长失真**(0.387 s 对 31 步、0.641 s 对 27 步,使回放预算必然中途
  到期)是**触发器**而非本缺陷;本方案在时长修对之后仍然必要——任何外来取消都可能踩缝。
- **`agent_server.ML:1919`、`:2135`** 的 `Exn.Exn _ => ()` 把 `update_cached_proof`/`l1_write`
  的 `ERROR`/`Par_Exn` 一并吞掉,注释却写"没有证明可写"——错误掩盖缺陷,与中断机制无关。
- **`Par_Exn.release_first` 把"全员被取消"报成崩溃**:一批并行任务若全部只是被取消而账被吃掉,
  `Par_Exn.make` 不归约成 `Isabelle_Thread.interrupt`,`release_first` 的 `plain_exn` 只滤 proper
  (`par_exn.ML:50-52`),Breakdown 被当作真异常重抛。受影响的是 `sledgehammer_solver.ML:1574,
  1666,1774` 三处 `Par_List`,§4.2 够不着;`par_exn.ML`/`par_list.ML` 属发行版,只能在我们的
  调用点外包一层。另案。
- **进程级 `Lazy.lazy` 的永久毒化**:`RPC.ML:198`、`Isa-REPL/library/REPL_aux.ML:284`,以及
  `Semantic_Embedding/Tools/simd_vector.ML:47,215`(`RPC.ML:189-191` 的写法抄自它)。作者判定
  无需处理。`Isa-REPL/REPL_aux.ML:234` 是不在编译路径上的旧副本,待删。

## 6. 实施顺序与验证门

1. 先做遮蔽的名字空间传播实验(一个最小的下游 theory 里 `ML \<open>Timeout.apply\<close>` 解析到
   带账版本即通过;失败则退回逐点改名加 CI 检查)。然后 `library/accounted_timeout.ML` 落地
   (判据内核 + `Accounted_Timeout` + 结构遮蔽);`race.ML` 改用判据内核并改述文件头残余 (b);
   §4.1 三处补丁拆除。**同一提交**。重启 REPL 编译验证。
2. **验证期临时计数(R3,作者裁决 2026-08-31)**:验证期内每次改判记一行(站点、预算、进入
   包装至改判的实际耗时、被改判的异常种类)到 `breakdown_probe.ML` 的同一日志文件,只计数,
   **不写 `Exception_Log`**;与探针同一窗口,**测试完成后一并删除**。稳态不记案的裁决不变。
3. 复跑曾外泄的回放场景(`Bucket_Hash.thy` 全篇)与全量评估(cslh19,`PhiEx_All.thy`)。
   **可判定的验收门**:(a) 命令层 Breakdown 条数相对改前显著下降(预期为零,依 §2 的分布);
   (b) 剩余每一条都能归因到三类允许来源之一并逐条记录——在包装动态范围之外落地、宿主为
   `future.ML:217`/`future.ML:237`/`command.ML:228`、§2(乙)的布尔折叠;出现无法归因的即为
   不通过。`breakdown_probe.ML` 的观测口径改为按宿主分类计数。
4. **纪律**:命令层 Breakdown 计数上升不是回退信号;把它压回去的唯一合法手段是修正机制,
   **绝不允许重新加回无条件吞 Breakdown 的 handler**——那正是 §4.1 刚拆掉的形状。
5. 验证通过后撤除 `breakdown_probe.ML` 及其六处调用与 R3 的临时计数(清单见
   `phi-system/Docs/GUARD_NITPICK_FALSIFY_PLAN.md` §26.2 丁)。
6. §4.6 上游报告独立推进。

## 7. 风险表

| 风险 | 方向 | 缓解 |
|---|---|---|
| 计时器开火**之后**落地的真实资源故障被改判成 `TIMEOUT` | 漏报灾难 | **已知且被作者接受的残余**;开火之前的故障在形状上不会被改判;上游报告 |
| 改判把一次外来取消降级成下游可吞的 `Timeout.TIMEOUT`(`reasoners.ML:926-929` 变 `NONE`;`sledgehammer_solver.ML:628,660-662` 继续搜;`race.ML:208,254` 记为 `Timed_Out`) | 欠取消(取消了却停不下来) | 判据已收紧到"本层计时器已开火";`race.ML` 残余 (b) 同步改述;单发式取消者(Isa-REPL kill)应改成"发了之后循环确认",另案 |
| 内外层计时器都开火时外层预算静默失效 | 欠取消 | `Timeout.apply` 既有语义,不引入帧栈;记入 §4.2 残余 |
| 拆 §4.1 三处补丁后未开火的 Breakdown 浮到 Minilang 命令层 | 可见度上升 | 作者裁决:当错误上报;§6 第 4 条纪律 |
| 遮蔽让 `Timeout.apply` 的语义在调用点上不再显式 | 可读性 | 模块头注释 + README;`raw_apply` 逃生名可 grep |
| `timed_seq`/`timed1_tac`(`reasoners.ML:928,936`,每次 `Seq.pull` 一层,30 ms 预算)上多两次 `Event_Timer` 加锁 | 性能 | 替换前后各测一次;不可接受则该档改用 `raw_apply` 并写明理由 |
| 验证期临时计数未撤 | 残留 | §6 第 5 条明列,与探针同批删除 |

## 8. 评审记录

- rev 1(2026-08-30):由三份并行调查综合(设计、对抗评审、源码求证)。
- rev 1 → rev 2(2026-08-31):四视角(并发正确性、优雅与最小性、覆盖与集成、忠实性与比例感)
  各一轮质问、四位全新辩护人各一轮辩护、一位裁判裁决(45 条意见,辩护人 31 条让步、13 条部分
  让步、0 条硬驳回)。裁判判 rev 1 不能进入批准流程,阻塞项四条:挂钟判据方向错(G1)、判据对
  `Par_Exn` 失明(G2)、验收门自相矛盾(G3)、§4.5 第一条病因被证伪(G8);另应修六条、建议
  四条、放宽提议三条。rev 2 的处置:G1 由 R1 解决;G2 提取中断族判据内核;G3 改写验收门;
  G4 三条实现纪律;G5 归属由 R1 自动解决、残余记录;G6 `race.ML` 文件头同一提交改述;G7 §4.1
  改为事实陈述并由作者裁决"当错误上报";G8、G9 由作者裁决从方案拿掉、挂号 §5;G10 §4.4 删除;
  G11 行号与计数全部更正;G12 §2 定性框架收窄;G13 (乙) 补时序;G14 挂号 §5。
- **作者裁决汇总(2026-08-30 至 31)**:结构名 `Accounted_Timeout`;改判不记案;R1 采纳;
  R2 采纳(含 `raw_apply` 逃生名);R3 采纳(仅验证期,测试完成后与探针一并删除);§4.4 删除;
  G7 当错误上报;G8、G9 不处理。
- 记录来源的澄清(2026-08-30):"外来取消恰逢自己 deadline 被吞成超时"(残余 (b))的记档出自
  **本项目**的 `race.ML` 文件头,不是 Isabelle 官方文档。官方记录的只有总设计(实现手册
  Interrupts 段:中断可以是 OOM/栈溢出/超时/线程信号/进程信号,异常层面不分辨)与
  Break/Breakdown 之分(NEWS 2025,quasi-error)。
- **实施记录(2026-08-31,§6 第 1、2 步)**:名字空间传播实验通过(子 theory `Main` 在前、遮蔽
  theory 在后,`Timeout.apply` 解析到遮蔽版本;负对照确认断言失败会报出)。中断族判据内核落为
  `structure Interrupt_Family`(`find_interrupt`/`contains_interrupt`/`all_breakdown`),与
  `Accounted_Timeout` 同文件;`Race` 不再导出 `contains_interrupt`,`reasoners.ML:1376` 与
  `sledgehammer_solver.ML` 的 `normalise` 改调内核,`classify` 里冗余的中断重抛删去。Minilang
  环境实测:计时器开火后的 Breakdown(裸的与全 Breakdown 的 `Par_Exn`)被改判 `TIMEOUT`,开火前
  的原样上抛,proper 中断容器不被认领,普通异常原样上抛。提交:`Performant_Isabelle_ML` 6556a85、
  `auto_sledgehammer` 03411bb、`Isa-Mini` 487c695、`phi-system` da0626a4、主仓库 f02dbfb。
  **与 §6 第 2 步的偏差**:`breakdown_probe.ML` 在实施时已不存在(另一会话撤除),R3 的临时计数
  改为 `Event_Log` 的独立类别 `accounted_timeout_claim`(每次改判一条:physical、预算、进入包装
  至改判的耗时、异常形态、任务名),写入器在临时文件 `library/accounted_timeout_probe.ML`,钩子是
  `Accounted_Timeout.claim_probe`;不写 `Exception_Log`;两者与钩子一并在 §6 第 5 步删除。
- **验收记录(2026-08-31,§6 第 3 步,`Bucket_Hash.thy` 全篇,本机 Phi_System_Base 基座 REPL)**:
  第一轮(proof store 大面积失效,4 个 AoA 会话重证,3762 s):命令层 Breakdown **0 条**,改判 0 次,
  `Exception_Log` 9 条 Breakdown 全部在 `Phi_Sledgehammer_Solver.normalise`(8,`Par_List.get_some`
  的并行输家)与 `guard-racer R-conv`(1)——输家被取消、账丢在输家自己计时器开火之前,按设计不
  认领,由 `Par_List`/race 引擎当取消处理,无一离开。第二轮(store 已修好,回放路径,137 s):
  命令层 Breakdown 0 条,改判 0 次,`Exception_Log` 0 条。门 (a)(b) 对该场景通过。全量
  `PhiEx_All.thy` 待 cslh19 空出后复跑。
- 一手核对的细节:`is_interrupt_proper` = 裸中断 ∨ `Interrupt_Break`;`Interrupt_Break` 亦可被
  直接构造(`isabelle_thread.ML:139` 起的五处),不经账本;`expose_interrupt_result` 的正当用途是
  兜住"计时器在身体返回后才开火"的窗口,不能简单移除,其缺陷仅在无条件清账 + 非中断分支丢弃
  账值(`isabelle_thread.ML:175-176`)。
