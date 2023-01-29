package de.uka.ilkd.key.java;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public interface SchemaJavaReader extends JavaReader {

    void setSVNamespace(Namespace<SchemaVariable> ns);
}
