  // {RULENAME}
  rule
    <k> {K} </k>                              // Current computation
    <s> ^regular </s>
    <exit-code> 1 </exit-code>                // Exit code of interpreter process
    <mode> NORMAL </mode>                     // Execution mode: VMTESTS or NORMAL
    <schedule> DEFAULT </schedule>            // Gas Schedule: DEFAULT or ALBE
    <checkGas> _ </checkGas>                  // Enables/disables gas check in test driver

    <well-formedness>
      <typeChecking> false </typeChecking>
      ...
    </well-formedness>

    // IELE Specific
    // =============

    <iele>

      // Mutable during a single transaction
      // -----------------------------------

      <output> {OUTPUT} </output>                    // Return registers of current call frame
      <callStack> {CALLSTACK} </callStack>           // Inter-contract call stack
      <interimStates> _ </interimStates>             // Checkpointed network state for rollback
      <substateStack> _ </substateStack>             // Checkpointed substate for rollback

      // A single contract call frame
      // ----------------------------
      <callFrame>
        // The loaded state of a IELE program
        <pgmDef> #loadCode(#dasmContract(#parseByteStack({CODE}), Main)) </pgmDef>
        <callDepth> {CALLDEPTH} </callDepth>         // Inter-contract call stack depth
        <localCalls> {LOCALCALLS} </localCalls>      // Intra-contract call stack

        // I_*
        <id> ACCT_ID </id>                           // Currently executing contract
        <caller> CALLER_ID </caller>                 // Contract that called current contract
        <callData> {CALLDATA} </callData>            // Copy of register arguments
        <callValue> {CALLVALUE} </callValue>         // Value in funds passed to contract

        // \mu_*
        <regs> {REGS} </regs>                           // Current values of registers
        <localMem> {LOCALMEM} </localMem>               // Current values of local memory
        <peakMemory> {PEAKMEM} </peakMemory>            // Maximum memory used so far in call frame
        <currentMemory> {CURRENTMEM} </currentMemory>   // Current memory used in call frame
        <fid> {FID} </fid>                              // Name of currently executing function
        <gas> {GAS} </gas>                              // Current gas remaining
        <previousGas> _ => _ </previousGas>             // Gas remaining prior to last decrease

        <static> false </static>                        // Whether the call frame came from a staticcall
      </callFrame>

      // A_* (execution substate)
      <substate>
        <selfDestruct> _ </selfDestruct>                // Set of contract ids that were destroyed by this transaction
        <logData> {LOG} </logData>                      // Log entries for this transaction
        <refund> {REFUND} </refund>                     // Refund for this transaction
      </substate>

      // Immutable during a single transaction
      // -------------------------------------

      <gasPrice> _ </gasPrice>                          // Price of gas for this transaction
      <origin> ORIGIN_ID </origin>                      // Sender of current transaction

      // I_H* (block information)
      <beneficiary> _ </beneficiary>                    // Miner of current block
      <difficulty> _ </difficulty>                      // Difficulty of current block
      <number> _ </number>                              // Number of current block
      <gasLimit> _ </gasLimit>                          // Gas limit of current block
      <gasUsed> _ </gasUsed>                            // Gas used by current block
      <timestamp> _ </timestamp>                        // Timestamp of current block
      <blockhash> _ </blockhash>                        // List of previous block's hashes

    </iele>

    // IELE Network Layer
    // ==================

    <network>

      // Accounts Record
      // ---------------

      <activeAccounts> {ACTIVEACCOUNTS} </activeAccounts> // Set of keys in the accounts cell.
      <accounts>
        <account>
          <acctID> ACCT_ID </acctID>                       // ID of account
          <balance> ACCT_BAL </balance>                    // Balance of funds in account
          <code> #dasmContract(#parseByteStack({CODE}), Main) </code>  // Disassembled contract of account
          <storage> {STORAGE} </storage>                   // Permanent storage of account (for sload/sstore)
          <nonce> _ </nonce>                               // Nonce of account
        </account>
        ...
      </accounts>

      // Transactions Record
      // -------------------

      <txOrder> _  </txOrder>            // Order of transactions in block
      <txPending> _ </txPending>          // Remaining transactions in block
      <messages> _ </messages>
    </network>

