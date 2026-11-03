-- A correct proof whose file also tries, WHILE IT IS BEING COMPILED, to write to three places.
-- Inside Comparator's sandbox only the first may succeed:
--   .lake/qrh_probe_inside       inside the project's .lake directory: allowed
--   qrh_probe_project            in the project directory, next to the challenge: must be denied
--   ../sandbox_write.outside     outside the project: must be denied
-- The self-test looks for the three files afterwards. The first one existing shows that this
-- code really ran; the other two missing shows that the sandbox Comparator set up held.
#eval show IO Unit from do
  for path in [".lake/qrh_probe_inside", "qrh_probe_project", "../sandbox_write.outside"] do
    try
      IO.FS.writeFile path "written during compilation by the sandbox control\n"
    catch _ => pure ()

theorem qrh_control (n m : Nat) : n + m = m + n := Nat.add_comm n m
