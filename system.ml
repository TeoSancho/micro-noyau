
let max_time_slices = 5   (* 0 <= t < max_time_slices *)
let max_priority    = 15  (* 0 <= p <= max_priority *)

let num_processes  = 32
let num_channels   = 128

let num_registers  = 5

type pid = int
type chanid = int
type value = int
type priority = int

type registers = {
  r0    : int;
  r1    : int;
  r2    : int;
  r3    : int;
  r4    : int;
}

type process_state =
    Free
  | BlockedWriting of chanid
  | BlockedReading of chanid list
  | Waiting
  | Runnable
  | Zombie

type process = {
  mutable parent_id   : pid;
  mutable state       : process_state;
  mutable slices_left : int;
  saved_context       : int array;
}

type channel_state =
    Unused
  | Sender of pid * priority * value
  | Receivers of (pid * priority) list

type state = {
  mutable curr_pid   : pid;
  mutable curr_prio  : priority;

  registers  : int array;

  processes  : process array;
  channels   : channel_state array;
  runqueues  : pid list array;
}

let get_registers { registers } = {
  r0 = registers.(0);
  r1 = registers.(1);
  r2 = registers.(2);
  r3 = registers.(3);
  r4 = registers.(4);
}

let set_registers {registers} { r0; r1; r2; r3; r4 } =
  registers.(0) <- r0;
  registers.(1) <- r1;
  registers.(2) <- r2;
  registers.(3) <- r3;
  registers.(4) <- r4

let get_current { curr_pid = c } = c

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

let decode { registers } =
  match registers.(0) with
  | 0 -> NewChannel
  | 1 -> Send (registers.(1), registers.(2))
  | 2 -> Recv [registers.(1);
               registers.(2);
               registers.(3);
               registers.(4)]
  | 3 -> Fork (registers.(1), registers.(2),
               registers.(3), registers.(4))
  | 4 -> Exit
  | 5 -> Wait
  | _ -> Invalid

let new_channel {registers; channels} =
  let rec new_channel i =
    if i >= num_channels then -1
    else if channels.(i) = Unused then (channels.(i) <- Receivers []; i)
    else new_channel (i + 1)
  in
  registers.(0) <- new_channel 0

let release_receiver {channels; processes} rid =
  let clear ch =
    channels.(ch) <-
      match channels.(ch) with
      | Receivers rs -> Receivers (List.filter (fun (pid, _) -> pid <> rid) rs)
      | v -> v
  in
  (match processes.(rid).state with
   | BlockedReading rchs -> List.iter clear rchs
   | _ -> assert false);
  processes.(rid).state <- Runnable

let send ({curr_pid; curr_prio; registers; processes; channels} as s) ch v =
  match channels.(ch) with
  | Sender _ | Unused -> (registers.(0) <- 0; false)

  | Receivers [] ->
      channels.(ch) <- Sender (curr_pid, curr_prio, v);
      processes.(curr_pid).state <- BlockedWriting ch;
      registers.(0) <- 1;
      true

  | Receivers ((rid, rprio)::rs) ->
      release_receiver s rid;
      let saved_registers = processes.(rid).saved_context in
      saved_registers.(0) <- 1;
      saved_registers.(1) <- ch;
      saved_registers.(2) <- v;
      registers.(0) <- 1;
      rprio >= curr_prio

let rec insert_receiver (id, prio) receivers =
  match receivers with
  | [] -> [(id, prio)]
  | (rid, rprio)::rs ->
      if prio > rprio
      then (id, prio) :: receivers
      else (rid, rprio) :: insert_receiver (id, prio) rs

let recv {curr_pid; curr_prio; registers; processes; channels} chs =
  let rec sender_ready chans =
    match chans with
    | [] -> None
    | ch::chs ->
        match channels.(ch) with
        | Sender (sid, sprio, sv) -> Some (ch, sid, sprio, sv)
        | _ -> sender_ready chs
  in
  match sender_ready chs with
  | Some (ch, sid, sprio, sv) ->
      channels.(ch) <- Receivers [];
      processes.(sid).state <- Runnable;
      registers.(0) <- 1;
      registers.(1) <- ch;
      registers.(2) <- sv;
      sprio >= curr_prio
  | None ->
      let rec add_to_receivers blocked chans =
        match chans with
        | [] -> blocked
        | ch::chs ->
            match channels.(ch) with
              Unused | Sender _ -> add_to_receivers blocked chs
            | Receivers rs ->
                channels.(ch) <-
                  Receivers (insert_receiver (curr_pid, curr_prio) rs);
                add_to_receivers (ch::blocked) chs
      in
      match add_to_receivers [] chs with
      | [] -> (registers.(0) <- 0; false)
      | bchs -> (processes.(curr_pid).state <- BlockedReading bchs; true)

let fork { curr_pid; curr_prio; registers; processes; runqueues }
         nprio d0 d1 d2 =
  let rec new_proc i =
    if i >= num_processes then None
    else if processes.(i).state = Free then
      let np = processes.(i) in
      np.parent_id <- curr_pid;
      np.state <- Runnable;
      np.slices_left <- max_time_slices;
      np.saved_context.(0) <- 2;
      np.saved_context.(1) <- curr_pid;
      np.saved_context.(2) <- d0;
      np.saved_context.(3) <- d1;
      np.saved_context.(4) <- d2;
      Some i
    else new_proc (i + 1)
  in
  match new_proc 0 with
  | None -> registers.(0) <- 0
  | Some npid -> begin
      registers.(0) <- 1;
      registers.(1) <- npid;
      runqueues.(nprio) <- runqueues.(nprio) @ [npid]
    end

let exit { curr_pid; curr_prio; registers; processes; runqueues } =
  let { parent_id } as p = processes.(curr_pid) in

  let f p = if p.parent_id = curr_pid then p.parent_id <- 1 in
  Array.iter f processes;

  runqueues.(curr_prio) <-
      List.filter (fun pid -> pid <> curr_pid) runqueues.(curr_prio);
  
  if processes.(parent_id).state = Waiting
  then begin
    processes.(parent_id).state <- Runnable;
    processes.(curr_pid).state <- Free;
    let saved_registers = processes.(parent_id).saved_context in
    saved_registers.(0) <- 1;
    saved_registers.(1) <- curr_pid;
    saved_registers.(2) <- registers.(0)
  end
  else processes.(curr_pid).state <- Zombie

let wait {curr_pid; registers; processes} =
  let rec already_dead has_child i =
    if i = num_processes then has_child, None
    else begin
      let { state; parent_id; saved_context} = processes.(i) in
      if state = Zombie && parent_id = curr_pid
      then true, Some (i, saved_context.(0))
      else already_dead (has_child || parent_id = curr_pid) (i + 1)
    end
  in
  match already_dead false 0 with
  | has_child, None ->
      if has_child
      then (processes.(curr_pid).state <- Waiting; true)
      else (registers.(0) <- 0; false)
  | _, Some (pid, v) ->
      processes.(pid).state <- Free;
      registers.(0) <- 1;
      registers.(1) <- pid;
      registers.(2) <- v;
      false

let save_context { registers; processes } pid =
  Array.blit registers 0 processes.(pid).saved_context 0 num_registers

let restore_context { registers; processes } pid =
  Array.blit processes.(pid).saved_context 0 registers 0 num_registers

let choose_process { runqueues; processes } =
  let rec find_within rq =
    match rq with
    | [] -> None
    | rid::rq' ->
        if processes.(rid).state = Runnable then Some rid
        else find_within rq'
  in
  let rec find prio =
    match find_within runqueues.(prio) with
    | None -> find (prio - 1)
    | Some pid -> prio, pid
  in
  find max_priority

let schedule ({curr_pid=prev_pid} as s) =
  let next_prio, next_pid = choose_process s in
  save_context s prev_pid;
  restore_context s next_pid;
  s.curr_pid <- next_pid;
  s.curr_prio <- next_prio

let timer_tick { curr_pid; curr_prio; processes; runqueues } =
  let ({ slices_left = remaining } as p) = processes.(curr_pid) in
  p.slices_left <- remaining - 1;
  if remaining = 0
  then (runqueues.(curr_prio) <-
          List.filter (fun pid -> pid <> curr_pid) runqueues.(curr_prio)
          @ [curr_pid]; true)
  else false

let transition ev ({curr_pid; registers; curr_prio} as s) =
  let reschedule =
    match ev with
    | Timer -> timer_tick s
    | SysCall ->
        match decode s with
        | Send (ch, v) -> send s ch v
        | Recv chs -> recv s chs
        | Fork (prio, d0, d1, d2) ->
            ((if prio <= curr_prio
              then fork s prio d0 d1 d2
              else registers.(0) <- 0); false)
        | Wait -> wait s
        | Exit -> (exit s; true)
        | NewChannel -> (new_channel s; false)
        | Invalid -> (registers.(0) <- -1; false)
  in
  if reschedule then schedule s

let init =
  let new_procs i =
    if i = 0 then {
      parent_id = 0;
      state = Runnable;
      saved_context = Array.make num_registers 0;
      slices_left = max_time_slices }
    else if i = 1 then {
      parent_id = 1;
      state = Runnable;
      saved_context = Array.make num_registers 0;
      slices_left = max_time_slices }
    else {
      parent_id = 0;
      state = Free;
      saved_context = Array.make num_registers 0;
      slices_left = 0 }
  in
  let new_queues i =
    if i = max_priority then [1]
    else if i = 0 then [0]
    else []
  in {
    curr_pid  = 0;
    curr_prio = max_priority;

    registers = Array.make num_registers 0;

    processes = Array.init num_processes new_procs;
    channels  = Array.make num_channels Unused;
    runqueues = Array.init (max_priority + 1) new_queues;
  }

