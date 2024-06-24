{-# OPTIONS --no-sized-types --safe #-}
open import constantparameters


module terminatedfiles (param : ConstantParameters) where


-- This file is terminated all Agda files for Solidity-style smart contracts.
-- The authors:  Fahad Alhabardi and Anton Setzer
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
open import libraries.ComplexModelLibrary
open import libraries.emptyLib
open import libraries.hoareTripleLibComplex
open import libraries.hoareTripleLibSimple
open import libraries.IOlibrary
open import libraries.logic
open import libraries.Mainlibrary
open import libraries.natCompare




                -----------------------------
                --      Simple Model       --
                -----------------------------

-- Ledger, commands, responses, smart contracts, contract, other defintions
open import Simple-Model.ledgerversion.Ledger-Simple-Model

-- library for the simple model
open import Simple-Model.library-simple-model.basicDataStructureWithSimpleModel

-- two examples for the simple model
open import Simple-Model.example.examplecounter
open import Simple-Model.example.solidityToagdaInsimplemodel-counterexample


                -----------------------------
                --  Simple verification    --
                -----------------------------


-- Verification programs and proves
  -- First program
open import Simple-Verification.hoareTripleVersfirstprogram
  -- Second program
open import Simple-Verification.hoareTripleVerssecondprogram


-- library for simple verification
open import libraries.hoareTripleLibSimple




               -----------------------------
               --   Complex model         --
               -----------------------------


-- Ledger in complex model
open import Complex-Model.ledgerversion.Ledger-Complex-Model
open import Complex-Model.terminating.ledger.Ledger-Complex-Model-improved-terminate

-- Commands, responses, and SmartContract in complex model
open import Complex-Model.ccomand.ccommands-cresponse  

-- library for complex model
open import libraries.Mainlibrary


-- examples for the complex model
open import Complex-Model.terminating.example.solidityToagdaIncomplexmodel-votingexample
open import Complex-Model.terminating.example.votingexample-complex
open import Complex-Model.terminating.example.votingexample-single-candidate
open import Complex-Model.terminating.example.executedvotingexample-single-candidate
open import Complex-Model.terminating.example.votingexample-multi-candidates
open import Complex-Model.terminating.example.executedvotingexample-multi-candidates


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




























