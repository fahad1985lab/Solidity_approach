open import constantparameters


module guidelines_verification (param : ConstantParameters) where


-- This file is guidelines for the code contained in the paper.
-- The authors:  Fahad Alhabardi and Anton Setzer
-- The title of the paper: Verification of Solidity-style Smart Contracts in Agda using Weakest Precondition
-- All files have been checked and worked  (Agda version 2.6.4.1) (Agda standard library version 2.0).


                ----------------------
                -- Root Directory   --
                ----------------------

open import basicDataStructure
open import constantparameters



                ----------------------
                --   libraries      --
                ----------------------
open import libraries.boolLib
open import libraries.emptyLib
open import libraries.logic
open import libraries.natCompare
open import libraries.naturalnumber


                -----------------------------
                --   Simple Verification   --
                -----------------------------

-- Verification programs and proves
  -- First program
open import Simple-Verification.hoareTripleVersfirstprogram
  -- Second program
open import Simple-Verification.hoareTripleVerssecondprogram


-- library for simple verification
open import libraries.hoareTripleLibSimple

-- Ledger, commands, and responses
open import Simple-Model.ledgerversion.Ledger-Simple-Model

-- library for simple model
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel




               -----------------------------
               --   Complex Verification  --
               -----------------------------


-- Verification programs and proves
  -- First program
open import Complex-Verification.hoareTripleVersfirstprogramcomplex
  -- Second program
open import Complex-Verification.hoareTripleVersSecondprogramcomplex

-- library for complex verification
open import libraries.hoareTripleLibComplex

-- Ledger in complex model
open import Complex-Model.ledgerversion.Ledger-Complex-Model

-- Commands and responses in complex model
open import Complex-Model.ccomand.ccommands-cresponse  

-- library for complex model
open import libraries.Mainlibrary




























