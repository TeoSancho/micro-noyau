
let max_time_slices = 5   (* 0 <= t < max_time_slices *)
let max_priority    = 15  (* 0 <= p <= max_priority *)

module type SYSTEM =
  sig
    type pid = int
    type state

    type registers = {
      r0    : int;
      r1    : int;
      r2    : int;
      r3    : int;
      r4    : int;
    }

    val get_registers : state -> registers
    val set_registers : state -> registers -> state

    val get_current : state -> pid

    type event =
        Timer
      | SysCall

    val transition : state -> event -> state

    val init : state
  end

module System =
  struct
    type pid = int
    type chanid = int
    type value = int
    type interrupt = int
    type priority = int

    type registers = {
      r0    : int;
      r1    : int;
      r2    : int;
      r3    : int;
      r4    : int;
    }

    type process_state =
        BlockedWriting of chanid
      | BlockedReading of chanid list
      | Waiting
      | Runnable
      | Zombie

    type process = {
      process_id    : pid;
      parent_id     : pid;

      state         : process_state;
      saved_context : registers;
      slices_left   : int;
    }

    type channel_state =
        Sender of pid * value
      | Receivers of (pid * priority) list

    type state = {
      currpid   : pid;
      currprio  : priority;

      registers : registers;

      runqueues : (priority * process list) list;
      channels  : (chanid * channel_state) list;
    }

    let get_registers { registers = r } = r
    let set_registers s r = { s with registers = r }
    let get_current { currpid = c } = c

    type event =
        Timer
      | SysCall

    type syscall =
        Send of chanid * value
      | Recv of chanid list
      | Fork of priority * value * value * value
      | Wait
      | Exit
      | NewChannel
      | Invalid

    let decode { r0; r1; r2; r3; r4 } =
      match r0 with
      | 0 -> NewChannel
      | 1 -> Send (r1, r2)
      | 2 -> Recv [r1; r2; r3; r4]
      | 3 -> Fork (r1, r2, r3, r4)
      | 4 -> Exit
      | 5 -> Wait
      | _ -> Invalid

    let processes { runqueues } =
      List.fold_left (fun xs (_, ps) -> ps @ xs) [] runqueues

    let process s pid =
      List.find (fun { process_id } -> process_id = pid) (processes s)

    let omap f =
      let rec go xxs =
        match xxs with [] -> []
        | x::xs -> match f x with None -> go xs | Some r -> r::go xs
      in go

    let upd_processes ({ runqueues } as s) f =
      { s with runqueues =
                 List.map (fun (prio, rq) -> (prio, omap f rq)) runqueues }

    let upd_process s pid f =
      let f ({process_id} as p) = Some (if pid = process_id then f p else p) in
      upd_processes s f

    let remove_process s pid =
      let f ({process_id} as p) = (if pid = process_id then None else Some p) in
      upd_processes s f

    let upd_channels ({ channels } as s) f =
      { s with channels = List.map f channels }

    let upd_channel s chid f =
      let f ((id, data) as ch) = if chid = id then f data else ch in
      upd_channels s f

    let upd_runqueues ({ runqueues } as s) f =
      { s with runqueues = List.map f runqueues }

    let upd_runqueue s prio f =
      let f ((qp, procs) as rq) = if qp = prio then (qp, f procs) else rq in
      upd_runqueues s f

    let set_register0 ({ registers = r } as s) v =
      { s with registers = { r with r0 = v } }

    let send ({currpid; runqueues; channels} as s) chid v =
      try
        match List.assoc chid channels with
        | Sender _ -> raise Not_found
        | Receivers [] ->
            let updc ((id, _) as ch) =
              if id = chid then (id, Sender (currpid, v)) else ch
            in
            let s' = upd_process s currpid
                      (fun p -> { p with state = BlockedWriting chid }) in
            true, { (set_register0 s' 1) with channels = List.map updc channels }
        | Receivers ((bid, _)::bs) ->
            let updc ch = match ch with
              (id, Receivers ws) -> (id, Receivers (List.remove_assoc bid ws))
            | _ -> ch
            in
            let s' =
              upd_process s bid
                (fun ({saved_context=sc} as p) ->
                    { p with state = Runnable;
                             saved_context = { sc with r0 = 1;
                                                       r1 = chid;
                                                       r2 = v }})
            in true, { s' with channels = List.map updc channels }
      with Not_found -> false, set_register0 s 0

    let rec insert_receiver (pid, prio) bs =
      match bs with
      | [] -> [(pid, prio)]
      | (bid, bprio)::bss when prio > bid -> (pid, prio)::(bid, bprio)::bss
      | bs::bss -> bs::insert_receiver (pid, prio) bss

    let recv ({currpid; registers=rs;
               currprio; runqueues; channels} as s) chids =

      let add_to_receivers ((chid, chst) as ch) =
        if List.mem chid chids
        then match chst with
             | Receivers rs ->
                (chid, Receivers (insert_receiver (currprio, currpid) rs))
             | _ -> assert false
        else ch in

      let rec sender_ready chs =
        match chs with
          [] -> None
        | (id, Sender (sid, v))::_ when List.mem id chids -> Some (id, sid, v)
        | _::chs -> sender_ready chs in

      match sender_ready channels with
      | None ->
          if List.exists (fun (chid, _) -> List.mem chid chids) channels
          then true, upd_channels s add_to_receivers
          else false, set_register0 s 0
      | Some (chid, sid, v) ->
          let s' =
            upd_process s sid
              (fun ({saved_context=sc} as p) ->
                 { p with state = Runnable; saved_context = { sc with r0 = 1 }})
          in
          true, { (upd_channel s' chid (fun _ -> (chid, Receivers []))) with
                    registers = { rs with r0 = 1; r1 = chid; r2 = v } }

    let next_process_id s =
      let f m {process_id=pid} = max m pid in
      1 + (List.fold_left f 0 (processes s))

    let fork ({currpid; registers = rs} as s) prio d0 d1 d2 =
      let newpid = next_process_id s in
      let newp = {
        process_id = newpid;
        parent_id = currpid;
        state = Runnable;
        saved_context = { r0 = 2; r1 = currpid; r2 = d0; r3 = d1; r4 = d2 };
        slices_left = max_time_slices } in
      { (upd_runqueue s prio (fun rq -> rq @ [newp]))
        with registers = { rs with r0 = 1; r1 = newpid } }

    let wait ({currpid; registers=rs; runqueues} as s) =
      let rec already_dead has_child procs =
        match procs with
        | { state = Zombie; parent_id=dpid;
            process_id=pid; saved_context = { r0 } } :: _ when dpid = currpid
          -> true, Some (pid, r0)
        | { parent_id } :: ps ->
              already_dead (has_child || parent_id=currpid) ps
        | [] -> has_child, None
      in
      match already_dead false (processes s) with
      | has_child, None ->
          if has_child
          then true, upd_process s currpid
                       (fun p -> { p with state = Waiting })
          else false, set_register0 s 0
      | _, Some (pid, v) ->
          false, { (remove_process s pid)
                   with registers = { rs with r0 = 1; r1 = pid; r2 = v }}

    let make_orphans s pid =
      let f ({parent_id=dpid} as p) =
        Some (if dpid = pid then { p with parent_id = 1 } else p)
      in upd_processes s f

    let exit ({currpid; registers={r0} } as s) =
      let { parent_id=dpid; state=pstate } = process s currpid in
      let s' = make_orphans s currpid in
      if pstate = Waiting
      then
        upd_process (remove_process s' currpid) dpid
          (fun ({ process_id; saved_context } as proc) ->
            { proc with state = Runnable;
                        saved_context = { saved_context with r0 = 1;
                                                             r1 = currpid;
                                                             r2 = r0 }})
      else upd_process s' currpid (fun p -> { p with state = Zombie })

    let next_channel_id {channels} =
      let f m (chid, _) = max m chid in
      1 + (List.fold_left f 0 channels)

    let newchannel ({registers; channels} as s) =
      let newch = next_channel_id s in
      { s with registers = { registers with r0 = newch };
               channels = (newch, Receivers [])::channels }

    let save_context ({ registers = r } as s) pid =
      upd_process s pid (fun p -> { p with saved_context = r})

    let restore_context s pid =
      let { saved_context } = process s pid in
      { s with registers = saved_context }

    let choose_process { runqueues } =
      let runnable { state } = (state = Runnable) in
      let has_runnable (_, queued) = List.exists runnable queued in
      match List.filter has_runnable runqueues with
      | (prio, { process_id }::_)::_ -> (prio, process_id)
      | _ -> assert false (* the idle thread is always Runnable *)

    let schedule ({currpid; runqueues} as s) =
      let s' = save_context s currpid in
      let nextprio, nextpid = choose_process s' in
      { (restore_context (save_context s currpid) nextpid)
          with currpid = nextpid; currprio = nextprio }

    let timer_tick ({ currpid; currprio } as s) =
      let ({ slices_left = remaining } as p) = process s currpid in
      let rec preempt queued =
        match queued with
        | [] -> [{ p with slices_left = max_time_slices }]
        | ({ process_id } as p)::ps ->
            if process_id = currpid then preempt ps else (p::preempt ps)
      in
      if remaining = 0
      then true, upd_runqueue s currprio (fun queued -> preempt queued)
      else false, upd_process s currpid
                    (fun p -> { p with slices_left = remaining - 1 })

    let transition ({currpid; registers=rs; currprio} as s) ev =
    let reschedule, s' =
      match ev with
      | Timer -> timer_tick s
      | SysCall ->
          match decode rs with
          | Send (ch, v) -> send s ch v
          | Recv chs -> recv s chs
          | Fork (prio, d0, d1, d2) ->
              if prio <= currprio
              then true, fork s prio d0 d1 d2
              else false, set_register0 s 0
          | Wait -> wait s
          | Exit -> true, exit s
          | NewChannel -> false, newchannel s
          | Invalid -> false, set_register0 s (-1)
    in
    if reschedule then schedule s' else s'

    let rec empty_queues idlep n =
      if n = 0 then [(n, [idlep])] else (n, [])::empty_queues idlep (n - 1)

    let init () =
      let nregs = { r0 = 0; r1 = 0; r2 = 0; r3 = 0; r4 = 0 } in
      let idlep = {
          process_id = 0;
          parent_id = 0;
          state = Runnable;
          saved_context = nregs;
          slices_left = max_time_slices;
        } in
      let initp = {
          process_id = 1;
          parent_id = 1;
          state = Runnable;
          saved_context = nregs;
          slices_left = max_time_slices;
        }
      in {
        currpid   = 0;
        registers = nregs;
        currprio  = max_priority;
        runqueues = (max_priority, [initp])
                    ::empty_queues idlep (max_priority - 1);
        channels  = [];
      }

  end

