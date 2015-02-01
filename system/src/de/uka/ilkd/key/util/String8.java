// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import java.io.UnsupportedEncodingException;
import java.util.Arrays;

/**
 * Re-implementation of String using only 8bit encoding
 * as compared to standard 16bit.
 * Only ASCII characters (7bit) are supported.
 * Immutable.
 * @author bruns
 *
 */
public class String8 implements CharSequence, java.io.Serializable {
    
    private static final long serialVersionUID = 5370917742980374037L;
    private final byte[] value;
    
    public String8 () {
        value = new byte[0];
    }
    
    private String8 (byte[] b) {
        value = b;
    }
    
    public String8 (CharSequence s, boolean checkValues) {
        value = new byte[s.length()];
        for (int i= 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (checkValues && c > Byte.MAX_VALUE)
                throw new IllegalArgumentException("Unsupported character \""+c+"\".");
            value[i] = (byte)c;
        }
    }
    
    public String8 (CharSequence s) {
        this(s, true);
    }

    @Override
    public char charAt(int index) {
        if ((index < 0) || (index >= value.length))
            throw new StringIndexOutOfBoundsException(index);
        return (char)value[index];
    }

    @Override
    public int length() {
        return value.length;
    }
    
    @Override
    public boolean equals (Object o) {
        if (o instanceof String8) {
            return Arrays.equals(value, ((String8)o).value);
        } else return false;
    }
    
    @Override
    public int hashCode () {
        return Arrays.hashCode(value);
    }
    
    @Override
    public String toString() {
        try {
            return new String(value, "US-ASCII");
        } catch (UnsupportedEncodingException e) {
            assert false;
            return null;
        }
    }

    @Override
    public String8 subSequence(int start, int end) {
        if (start < 0)
            throw new StringIndexOutOfBoundsException(start);
        if (end >= value.length)
            throw new StringIndexOutOfBoundsException(start);
        if (start > end)
            throw new IllegalArgumentException("Negative sequence length: "+(end-start));
        return new String8(Arrays.copyOfRange(value, start, end));
    }
    
    public String8 concat (String8 s) {
        final byte[] v = Arrays.copyOf(value, value.length+s.length());
        for (int i= 0; i < s.length(); i++)
            v[i+value.length] = s.value[i];
        return new String8(v);
    }

}