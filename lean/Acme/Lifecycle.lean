import Lentil.Managed
import Grpc.Services.Health

namespace Acme.Lifecycle

/-- Probe names have independent meanings: readiness controls admission;
liveness remains serving during graceful drain. -/
def healthResource : IO (Lentil.Resource Grpc.Services.Health.Service) := do
  let health ← Grpc.Services.Health.Service.new
  health.setNotServing ""
  health.setNotServing "readiness"
  health.setServing "liveness"
  return { value := health, hooks := { release := health.shutdown } }

def markReady (health : Grpc.Services.Health.Service) : IO Unit := do
  health.setServing ""
  health.setServing "readiness"

/-- The listener stop action is attempted even if withdrawing readiness fails. -/
def quiesce (health : Grpc.Services.Health.Service) (stopAdmission : IO Unit) : IO Unit := do
  try
    health.setNotServing ""
    health.setNotServing "readiness"
  finally
    stopAdmission

end Acme.Lifecycle
