package de.uka.ilkd.key.java;

import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class SchemaJP2KeY extends JavaService implements SchemaJavaReader {
    private static final Logger LOGGER = LoggerFactory.getLogger(SchemaJP2KeY.class);

    /** the namespace containing the program schema variables allowed here */
    protected Namespace<SchemaVariable> svns;

    public SchemaJP2KeY(Services services, NamespaceSet nss) {
        super(services, nss);
    }

    public void setSVNamespace(Namespace<SchemaVariable> svns) {
        this.svns = svns;
    }

    /**
     * there is no need to parse special classes in this case, so this is empty
     *
     * @see JavaService#parseSpecialClasses()
     */
    public void parseSpecialClasses() {
    }
}
