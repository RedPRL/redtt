let termination_queue = Queue.create ()

let on_termination f = Queue.add f termination_queue

let terminated () =
  Queue.iter (fun f -> f ()) termination_queue
