//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Position;


public class PositionedString {
   
    public final String text;
    public final String fileName;
    public final Position pos;

    
    public PositionedString(String text, String fileName, Position pos) {
        assert text != null;
        if(fileName == null) {
            fileName = "no file";
        }
        if(pos == null) {
            pos = Position.UNDEFINED;
        }
        this.text = text;
        this.fileName = fileName;
        this.pos = pos;
    }
    
    
    public PositionedString(String text, String fileName) {
        this(text, fileName, null);
    }
    
    
    public PositionedString(String text) {
        this(text, null);
    }
    
    
    public String toString() {
        return text + " (" + fileName + ", " + pos + ")";
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof PositionedString)) {
            return false;
        }
        PositionedString ps = (PositionedString) o;
        return text.equals(ps.text) 
               && fileName.equals(ps.fileName) 
               && pos.equals(ps.pos);
    }
    
    
    public int hashCode() {
        return text.hashCode() + fileName.hashCode() + pos.hashCode();
    }
}
