/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Action
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.EmptyReject
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.PositiveReject
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Attempt
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Reject
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.Loop
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Gate.LoopReject
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.PositiveLoopReject
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Execution.Family
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Evaluator
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Hoare
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Pure
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Stage
import Complexitylib.Circuits.Encoding.Machine.Core.Internal.Tape

/-!
# Streaming evaluator proof internals

Internal aggregation module for the evaluator's action, exact execution,
successful and rejecting gate loops, total tagged-family semantics, quadratic
core and end-to-end contracts, and tape-cursor proof seams.
-/
