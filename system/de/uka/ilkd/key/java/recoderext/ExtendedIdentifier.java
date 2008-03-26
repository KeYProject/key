package de.uka.ilkd.key.java.recoderext;

/** 
 * an extended identifier that excepts hash symbols in its name
 * but not as first character
 */
public class ExtendedIdentifier extends recoder.java.Identifier {
    /**
     * generated serialVersionUID
     */
    private static final long serialVersionUID = 1L;

    public ExtendedIdentifier(String arg0) {
        super(arg0);
    }

    public void setText(String text) {
        if (text.charAt(0)=='#') {
            throw new IllegalArgumentException
                ("No hash symbol allowed as first element in variable" +
                            "identifiers");
        } else if (text.charAt(0)=='<') {
            throw new IllegalArgumentException
            (text + " is no valid extended identifier.");
        }
        id=text.intern();
    }
    
    public ExtendedIdentifier deepClone() {
        return new ExtendedIdentifier(id);
    }
}
