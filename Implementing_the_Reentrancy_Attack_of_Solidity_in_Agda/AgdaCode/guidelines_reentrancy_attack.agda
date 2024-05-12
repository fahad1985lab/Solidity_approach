open import constantparameters


module guidelines_reentrancy_attack (param : ConstantParameters) where


-- This file is guidelines for the code contained in the paper.
-- The authors:  Fahad Alhabardi and Anton Setzer
-- The title of the paper: Verification of Solidity-style Smart Contracts in Agda using Weakest Precondition
-- All files have been checked and worked (Agda version 2.6.4.1) (Agda standard library version 2.0).
-- In order to open these files you need to load all files and by clicking on opening iomprt statment you can get to the diffrent funds.




           --- Sect V. THE REENTRACY ATTACK

                ------------------------
                --   reentracy attack --
                ------------------------
-- Ledger

open import Complex-Model.ledgerversion.Ledger-Complex-Model-with-reentrancy-attack

-- Example

open import Complex-Model.example.reentrancy-attack.reentrancy-attack

-- Execute the example of reentrancy attack
open import Complex-Model.example.reentrancy-attack.executed-reentrancy-attack

-- commands and responses in the complex model version 2

open import Complex-Model.ccomand.ccommands-cresponse

-- Interactive program in Agda

open import Complex-Model.IOledger.IOledgerReentrancyAttack



                ----------------------
                -- Root Directory   --
                ----------------------

open import basicDataStructure


                ----------------------
                --   libraries      --
                ----------------------
open import libraries.Mainlibrary-new-version
open import libraries.IOlibrary-new-version
open import libraries.emptyLib
open import libraries.natCompare




































