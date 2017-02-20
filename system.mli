
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
val set_registers : state -> registers -> unit

val get_current : state -> pid

type event =
    Timer
  | SysCall

val transition : event -> state -> unit

val init : state

