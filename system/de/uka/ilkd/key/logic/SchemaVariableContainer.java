package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ListOfSchemaVariable;


/**
 * Implement this interface for terms that contain 
 * SchemaVariables that would otherwise not be collected. 
 * 
 * @author mulbrich
 *
 */
public interface SchemaVariableContainer {

    ListOfSchemaVariable collectSV(ListOfSchemaVariable varList);

}
