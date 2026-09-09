import Acme.Lifecycle

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw <| IO.userError message

def main : IO Unit := do
  let scope ← Lentil.Scope.new
  let health ← scope.acquire "health" Acme.Lifecycle.healthResource
  check ((← health.checkStatus? "readiness") == some .notServing) "startup readiness"
  check ((← health.checkStatus? "liveness") == some .serving) "startup liveness"
  let draining ← IO.Promise.new
  let release ← IO.Promise.new
  let stopped ← Std.Mutex.new false
  let databaseClosed ← Std.Mutex.new false
  let _ ← scope.acquire "database" (pure { value := (), hooks := {
    release := databaseClosed.atomically (set true) } })
  let _ ← scope.acquire "listener" (pure { value := (), hooks := {
    quiesce := Acme.Lifecycle.quiesce health (stopped.atomically (set true))
    drain := do draining.resolve (); IO.wait release.result! } })
  Acme.Lifecycle.markReady health
  scope.markReady
  check ((← health.checkStatus? "readiness") == some .serving) "running readiness"
  let closing ← IO.asTask scope.close
  IO.wait draining.result!
  check (← stopped.atomically get) "listener was not stopped"
  check (!(← databaseClosed.atomically get)) "database released before listener drained"
  check ((← health.checkStatus? "") == some .notServing) "overall readiness during drain"
  check ((← health.checkStatus? "readiness") == some .notServing) "readiness during drain"
  check ((← health.checkStatus? "liveness") == some .serving) "liveness during drain"
  release.resolve ()
  (← IO.ofExcept (← IO.wait closing)).throwIfFailed
  check (← databaseClosed.atomically get) "database not released"
  check ((← health.checkStatus? "liveness") == some .notServing) "terminal liveness"
  Acme.Lifecycle.markReady health
  check ((← health.checkStatus? "readiness") == some .notServing) "health resurrected after close"
  IO.println "Acme lifecycle health and database ownership: passed"
