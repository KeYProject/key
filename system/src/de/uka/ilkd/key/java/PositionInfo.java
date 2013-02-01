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
        this.fileName=simplifyPath(fileName);//bugfix:2009.09.17
    }
    
    /** If the path contains the substring "/../", then this method tries to 
     * simplify the path by removing this substring and the preceeding directory name
     * to that substring. Otherwise java.io.FileReader would have a problem.
     * E.g. Input "/A/B/../D" - Output "/A/D"
     * @author gladisch*/
    private static String simplifyPath(String path){
	if(path==null || path.length()==0)
	    return path;
	int idx = path.indexOf("/../");
        while(idx > 0){
	    int pre= path.lastIndexOf("/", idx-1);
	    if(pre!=-1){
		path = path.substring(0, pre) + path.substring(idx+3);
	    }
	    idx = path.indexOf("/../");
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
