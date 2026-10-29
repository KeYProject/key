// Named spec cases use the JMLtk-native form `[behavior] <name>:` (an identifier prefix).
// JMLtk parses it into JmlContract.name; KeY carries it to the operation contract name
// (ContractLoadingTests.nameClauseCarriesContractName).
public class NameClause {

    int x;

    /*@ public normal_behavior
      @ CaseA:
      @   ensures \result == x;
      @*/
    public int m() { return x; }
}
