requires "iele.k"
requires "iele-binary.k"

module VERIFICATION
    imports IELE
    imports IELE-BINARY

    syntax IeleName ::= "totalSupply" [token]
                      | "balanceOf"   [token]
                      | "allowance"   [token]


    // Temporary solution to avoid reasoning about gas
    syntax Int ::= "#infinity" [function]
 // -------------------------------------
    rule #infinity -Int _ => #infinity
    rule #infinity >=Int _ => true
    rule #infinity <Int _ => false


    rule A >>Int 0   => A

    syntax Int ::= #mapKey(Int, Int) [function]
 // -------------------------------------------
    rule #mapKey(REGION, N) => (REGION <<Int 160) |Int (N modInt pow160) 

endmodule
