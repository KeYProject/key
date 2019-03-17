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

package de.uka.ilkd.key.java;

import java.io.File;

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
        this.fileName=simplifyPath(fileName);//bugfix:2009.09.17
    }
    
    /** If the path contains the substring "/../", then this method tries to 
     * simplify the path by removing this substring and the preceeding directory name
     * to that substring. Otherwise java.io.FileReader would have a problem.
     * E.g. Input "/A/B/../D" - Output "/A/D"
     * @author gladisch*/
    private static String simplifyPath(String path) {
        if (path != null && !path.isEmpty()) { 
            path = new File(path).toURI().normalize().getPath();
        }
        return path;
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

    /**
     * Creates a new PositionInfo from joining the intervals of the given PositionInfos.
     * The file informations have to match, otherwise null is returned.
     * @param p1 the first PositionInfo
     * @param p2 the second PositionInfo
     * @return a new PositionInfo starting at the minimum of the two start positions and
     * ending at the maximum of the two end positions.
     */
    public static PositionInfo join(PositionInfo p1, PositionInfo p2) {
        if (p1 == null && p2 == null) {
            return null;
        } else if (p1 == null) {
            return p2;
        } else if (p2 == null) {
            return p1;
        }

        // -> p1 and p2 not null
        if (p1 == UNDEFINED) {
            return p2;
        } else if (p2 == UNDEFINED) {
            return p1;
        }

        // -> p1 and p2 != UNDEFINED
        Position start;
        Position end;
        if (p1.startPos != Position.UNDEFINED && !p1.startPos.isNegative()
                &&  p1.startPos.compareTo(p2.startPos) < 0) {
            start = p1.startPos;
        } else {
            start = p2.startPos;
        }
        if (p1.endPos != Position.UNDEFINED && !p1.endPos.isNegative()
                && p1.endPos.compareTo(p2.endPos) > 0) {
            end = p1.endPos;
        } else {
            end = p2.endPos;
        }
        // TODO: join relative position as well
        PositionInfo pi = new PositionInfo(Position.UNDEFINED, start, end, p1.getFileName());
        return pi;
    }

    /**
     * Checks if start and end position are both defined and in valid range.
     * @return true iff start and end are valid
     */
    public boolean startEndValid() {
        return startPos != Position.UNDEFINED && !startPos.isNegative()
                && endPos != Position.UNDEFINED && !endPos.isNegative();
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