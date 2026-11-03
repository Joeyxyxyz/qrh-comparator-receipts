-- Right statement, but proved from an axiom that is not on the permitted list: must be rejected.
axiom qrh_helper {α : Sort u} : α

theorem qrh_control (n m : Nat) : n + m = m + n := qrh_helper
