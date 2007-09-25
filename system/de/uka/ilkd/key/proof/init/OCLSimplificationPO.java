package de.uka.ilkd.key.proof.init;

/**
 * Proof obligations resulting from the OCL Simplification implement this interface.
 * Currently the main reason is to avoid some dependencies on Together OpenAPI which 
 * make it impossible to compile KeY without Together.
 */

public interface OCLSimplificationPO {

    /**
     * Adds OCL types, OCL operations, and model properties to the
     * name spaces of the initial configuration.
     * Can as well be hard-coded, since they are needed for all
     * OCL simplification. Also avoids trouble with taclet parser.
     * @param initConf The initial configuration whose set of name
     * spaces needs to be updated.
     */
    void createNamespaceSet(InitConfig initConf);

}
