/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Bounds
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Out
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Pure
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Rewind
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Scan
import Complexitylib.Models.TuringMachine.Subroutines.BinaryRippleAdd.Internal.Sem

/-!
# Linear-time canonical binary addition -- proof internals

This aggregation module collects the pure arithmetic, scan, rewind, resource,
and output-discipline proofs used by the public surface.
-/
