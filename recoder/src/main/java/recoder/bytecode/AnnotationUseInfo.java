/*
 * Created on 27.05.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 */
package recoder.bytecode;

import recoder.abstraction.AnnotationUse;
import recoder.abstraction.ElementValuePair;

import java.util.List;

/**
 * @author gutzmann
 */
public class AnnotationUseInfo implements AnnotationUse {
    protected List<ElementValuePair> elementValuePairs;

    protected String fullAnnotationTypeName;

    /**
     * @param accessFlags
     * @param name
     */
    public AnnotationUseInfo(String fullName, List<ElementValuePair> evpl) {
        super();
        this.elementValuePairs = evpl;
        this.fullAnnotationTypeName = fullName;
    }

    public List<ElementValuePair> getElementValuePairs() {
        return elementValuePairs;
    }

    private String getParamStr() {
        StringBuffer res = new StringBuffer();
        boolean first = true;
        for (ElementValuePair evp : elementValuePairs) {
            if (!first)
                res.append(",");
            first = false;
            res.append(evp.toString());
        }
        return res.toString();
    }

    public String toString() {
        return "@" + getFullReferencedName() + "(" + getParamStr() + ")";
    }

    public String getFullReferencedName() {
        return fullAnnotationTypeName;
    }

    public String getReferencedName() {
        return fullAnnotationTypeName.substring(fullAnnotationTypeName.lastIndexOf('.') + 1);
    }
}
