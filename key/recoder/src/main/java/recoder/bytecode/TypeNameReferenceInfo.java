package recoder.bytecode;

public class TypeNameReferenceInfo {
    private final String referencedName;

    public TypeNameReferenceInfo(String trname) {
        this.referencedName = trname;
    }

    public String getReferencedName() {
        return referencedName;
    }

}
