// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.speclang;

import antlr.Token;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.label.TermLabel;

/**
 * A string with associated position information (file and line number). The
 * position information is used for error reporting.
 */
public class PositionedString {
   
    public final String text;
    public final String fileName;
    public final Position pos;

    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST =
            new ImmutableArray<TermLabel>();

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
    
    public PositionedString(String text, Token t){
        this(text, t.getFilename(), new Position(t.getLine(),t.getColumn()));
    }
    
    public PositionedString(String text, org.antlr.runtime.Token t){
        this(text, t.getInputStream().getSourceName(), new Position(t.getLine(),t.getCharPositionInLine()));
    }
    
    public PositionedString(String text, String fileName) {
        this(text, fileName, null);
    }
    
    
    public PositionedString(String text) {
        this(text, (String)null);
    }


    public PositionedString prepend(String text) {
        return new PositionedString(text + this.text.trim(), this.fileName, this.pos);
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

    /**
     * returns true if the positioned string is labeled
     */
    public boolean hasLabels() {
        return false;
    }

    /**
     * checks if the given label is attached to the positioned string
     * @param label the ITermLabel for which to look (must not be null)
     */
    public boolean containsLabel(TermLabel label) {
        return false;
    }

    /**
     * returns list of labels attached to this positioned string
     * @return list of labels (maybe be empty but never <code>null</code>
     */
    public ImmutableArray<TermLabel> getLabels() {
        return EMPTY_LABEL_LIST;
    }

    public PositionedLabeledString label(ImmutableArray<TermLabel> labels) {
        return new PositionedLabeledString(text, fileName, pos, labels);
    }

    public PositionedLabeledString label(TermLabel label) {
        return new PositionedLabeledString(text, fileName, pos, label);
    }
}
