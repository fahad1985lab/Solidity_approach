# This Git repository contains five Agda codes:

1- Developing Two Models of the Solidity-style Smart Contracts (chapter 6).

2- Simulating Two Models of Solidity-style Smart Contracts (chapter 7).

3- Verifying Solidity-style Smart Contracts (chapter 8).

4- Implementing the Reentrancy Attack of Solidity in Agda (chapter 9).

5- Safe Version of the code.




## Agda and Agda standard library versions

| Name                          | Version |
| ------------------------------| ------------- |
| Agda                          | `2.6.4.1`     |
| Agda standard library version |  `2.0`        |



 ## Authors and Licence
 * By 
 Fahad F. Alhabardi and [Anton Setzer](https://www.cs.swan.ac.uk/~csetzer/).
 
 
 * Licensed under a [GNU General Public License v3.0](https://www.gnu.org/licenses/gpl-3.0.en.html).
 
 
-----------------------------------

## Demonstration of Blockchain Simulators (chapter 7): 

* Simple Blockchain simulator (a simple counter).\
  The screenshot below will execute the following commands in sequence:

    * Select: `Option 1`, to execute at address `1` function `counter` with argument `1`.\
      The result will be `nat 0` (returning the content of the variable counter). 
    * Select: `Option 2`, to check a balance at address `1`.\
      This will return the balance at address `1`, which is 40 wei.
    * Select: `Option 3`, to change the calling address by entering a new calling address, `1`\
      and then calling the `increment` function with argument `0`.\
      The result will be `nat 1`.
    * Select: `Option 1`, to check function `counter` at address `1` after incrementing our counter.\
      The result will be `nat 1`.

![simple](https://github.com/fahad1985lab/A_simulator_of_Solidity-style_smart_contracts_in_the_theorem_prover_Agda/assets/77390330/3091812b-4412-4be7-8bef-ecc2fd5de0fb)



* Complex Blockchain simulator (basic voting example)\
  The screenshot below will execute the following commands in sequence:

    * Select: `Option 3`, to change the calling address to address `1`\
      	      and execute function addVoter with argument `nat 1` at address `1`.\
	      This will add voter `1`.  
    * Select: `Option 4`, to update the gas limit to `30` wei.
    * Select: `Option 5`, to check the gas limit after updating.\
      	      The result will be `30` wei.  
    * Select: `Option 6`, to check the pure function `checkVoter` with argument `nat 1`.\
      	      This returns `theMsg 1` for true.
    * Select: `Option 6`, to check the counter (number of votes), and we get `theMsg 0`,\
      	      i.e. number of votes is 0.
    * Select: `Option 1`, to call from address 1 function `vote` with argument `nat 1`.\
      	      This will return `nat 1`.
    * Select: `Option 6`, to check the pure function `checkVoter` with argument `nat 1`.\
      	      We get `theMsg 0` for false,\
	      which means voter 1 is (having voted) no longer allowed to vote. 
    * Select: `Option 6`, to check the pure function `counter`,\
      	      and we get `theMsg 1`, i.e. number of votes is 1.
    * Select: `Option 1`, to try to vote again (argument `nat 1`),\
      	      and this time, we get an error, because voter 1 is no longer allowed to vote.

![complex](https://github.com/fahad1985lab/A_simulator_of_Solidity-style_smart_contracts_in_the_theorem_prover_Agda/assets/77390330/840fb1a9-8d17-491a-ab62-c6ad324b4e80)
  


------------------------------


## Demonstration of Blockchain Simulator for the reentrancy attack (chapter 9): 


* Reentrancy attack simulator (example)\
  The screenshot below will execute the following commands in sequence:

    * Select: `Option 3`, to update the amount sent to `25000` wei.  
    * Select: `Option 4`, to check the amount sent.\
               This returens `The amount sent is 25000 wei`.
    * Select: `Option 5`, to check the balances for address `0` before making the reentrancy attack.\
      	      The result is `The available money is 100000 wei in address 0`  
    * Select: `Option 5`, to check the balances for address `1` before making the reentrancy attack.\
      	      The result is `The available money is 0 wei in address 1`
    * Select: `Option 5`, to check the balances for address `2` before making the reentrancy attack.\
      	      The result is `The available money is 26000 wei in address 2`
    * Select: `Option 6`, to update the gas limit to `250` wei in order to do the reentrancy attack.\
             This returns `The gas amount has been updated successfully`.
	     `The new gas amount is  250 wei and the old gas amount is 100 wei`
    * Select: `Option 7`, to check the gas limit after updating the gas limit.
      	      This returns `The gas limit is 250 wei`.
    * Select: `Option 2`, to change the calling address by entering a new address `2`
               then by entering called address `1` to call the `attack` function with aregument `25000`.\
	      This is result as following:\
	        *  The inital address is `2` \
                *  The called address is `1` \
                *  The amount sent is `25000` wei\
                *  The argument of the function name is (`nat 25000`)\
                *  The remaining gas is `66` wei and the gas used is `184` wei ,  \
                *  The function returned (`theMsg 0`) , \
                *  The list of events: 
              	      
	      
                    deposit `+25000` wei at address `0` for address `1`,  New balance at address `0` is `125000` wei 
                    Balance at address `0`  = `125000` wei.
                     withdraw `-25000` wei.
                    Balance at address 0  = `100000` wei.
                     withdraw `-25000` wei.
                    Balance at address `0`  = `75000` wei.
                     withdraw `-25000` wei.
                    Balance at address `0`  = `50000` wei.
                     withdraw `-25000` wei.
                    Balance at address `0`  = `25000` wei.
                     withdraw `-25000` wei.



              *  Current balance at address `0`  = `0` wei
              *  Current balance at address `1`  = `0` wei
              *  Current balance at address `2`  = `125750` wei

## Steps to run the simulator of the reentrancy attack under Emacs (GUI)
* First step  : Load this file (reentrancy-attack.agda) under this path (ReentrancyAttack/AgdaCode/Complex-Model/example/reentrancy-attack
/reentrancy-attack.agda) using `(Ctrl+c Ctrl+l)` or choose from the menu `(Agda then Load)`
* Second step : Compile the file using `(ctrl+c ctrl+x ctrl+c)` or choose from the menu `(Agda then compile)` and enter GHC. Then you will receive this message `The module was successfully compiled with backend GHC.`
* Third step  : Use `(Esc-x)` and write shell
* Fourth step : Use `(cd ..)` until arriving at this directory (~/Desktop/Verification_of_Solidity-style_smart_contracts_in_Agda_using_weakest_precondition) then type ./reentrancy-attack to run the interface as shown the process below:



![reentrancy_attacklast](https://github.com/fahad1985lab/verification_models_reentrncyattack/assets/77390330/9eadaddb-2d28-4b09-837e-aacc32e75629)



