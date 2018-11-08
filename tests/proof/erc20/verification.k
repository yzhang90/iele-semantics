requires "iele.k"
requires "iele-binary.k"

module VERIFICATION
    imports IELE
    imports IELE-BINARY

    syntax IeleName ::= "totalSupply"  [token]
                      | "balanceOf"    [token]
                      | "allowance"    [token]
                      | "approve"      [token]
                      | "transfer"     [token]
                      | "transferFrom" [token]

    // Temporary solution to avoid reasoning about gas
    syntax Int ::= "#infinity" [function]
 // -------------------------------------
    rule #infinity -Int _ => #infinity
    rule #infinity >=Int _ => true
    rule #infinity <Int _ => false


    rule A >>Int 0   => A

    syntax Int ::= #mapKey( Int, Int ) [function]
 // ---------------------------------------------
    rule #mapKey(REGION, N) => (REGION <<Int 160) |Int (N modInt pow160)


    syntax Int ::= "#approvalEvent" [function]
                 | "#transferEvent" [function]
 // ----------------------------------------
    rule #approvalEvent => #parseHexWord("0x7134692B230B9E1FFA39098904722134159652B09C5BC41D88D6698779D228FF")
    rule #transferEvent => #parseHexWord("0xF099CD8BDE557814842A3121E8DDFD433A539B8C9F14BF31EBF108D12E6196E9")

    syntax Topics ::= #topics ( Ints )
 // ----------------------------------

    syntax SubstateLogEntry ::= #eventLog ( Int , Topics , Bytes ) [function]
 // -----------------------------------------------------------------------
    rule #eventLog(ACCT_ID, TOPICS, DATA) => { ACCT_ID | #getEventTopics(TOPICS) | DATA }

    syntax List ::= #getEventTopics( Topics ) [function]
 // --------------------------------------------------
    rule #getEventTopics(#topics(TOPIC, TOPICS)) => ListItem(TOPIC) #getEventTopics(#topics(TOPICS))
    rule #getEventTopics(#topics(.Ints)) => .List

endmodule
