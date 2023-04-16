package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.java.recoderext.adt.MethodSignature;
import de.uka.ilkd.key.logic.op.SchemaVariable;

public class MethodSignatureSVWrapper extends MethodSignature implements SVWrapper {

    private static final long serialVersionUID = -4381850332826267659L;
    private SchemaVariable method;

    public MethodSignatureSVWrapper(SchemaVariable l) {
        super(null, null);
        method = l;
    }

    public SchemaVariable getSV() {
        return method;
    }

    public void setSV(SchemaVariable sv) {
        method = sv;
    }

    public String toString() {
        return String.valueOf(method);
    }
}
