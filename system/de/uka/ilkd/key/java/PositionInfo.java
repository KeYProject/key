// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

/**
 * represents a group of three Positions: relativePosition,
 * startPosition, endPosition
 */
public class PositionInfo {

    final Position relPos;
    final Position startPos;
    final Position endPos;

    String fileName=null;
    protected String parentClass;

    public final static PositionInfo UNDEFINED=new PositionInfo();

    private PositionInfo() {
	this.relPos=Position.UNDEFINED;
	this.startPos=Position.UNDEFINED;
	this.endPos=Position.UNDEFINED;
    }

    public PositionInfo(Position relPos, Position startPos, Position endPos) {
	this.relPos=relPos;
	this.startPos=startPos;
	this.endPos=endPos;
    }
    
    public PositionInfo(Position relPos, Position startPos, Position endPos, String fileName) {
        this.relPos=relPos;
        this.startPos=startPos;
        this.endPos=endPos;
        this.fileName=fileName;
    }

    public Position getRelativePosition() {
	return relPos;
    }

    public Position getStartPosition() {
	return startPos;
    }

    public Position getEndPosition() {
	return endPos;
    }

    public String getFileName(){
	return fileName;
    }

    /** this violates immutability, but the method is only called
      * right after the object is created...
      */
    protected void setParentClass(String s) {
        parentClass = s;
    }
    
    /** get the class the statement originates from */
    public String getParentClass() {
        return parentClass;
    }

    public String toString(){
	if (this==PositionInfo.UNDEFINED) 
            return "UNDEFINED";
	else return (fileName+" rel. Pos: "+relPos+" start Pos: "+
                    startPos+" end Pos: "+endPos);
    }

}
