/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseControl
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseDirect
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseImm
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseLoad
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.Instruction.DenseStore

/-!
# Dense-overlay RAM instruction kernels

This module collects the concrete positive-tag instruction simulators and
their exact Hoare/time contracts.
-/
