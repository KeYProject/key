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

/** 
 * Created on: Mar 17, 2011
 */
package de.uka.ilkd.key.smt.lang;

import java.util.LinkedList;
import java.util.List;

/**
 *
 *
 * @author Aboubakr Achraf El Ghazi
 *
 */
public class SMTFunction {
	
	protected String comment;

    public String getComment() {
		return comment;
	}

	public void setComment(String comment) {
		this.comment = comment;
	}

	protected String id;
    protected List<SMTSort> domainSorts;
    protected SMTSort imageSort;

    /**
     * @param id
     * @param domainSorts
     */
    public SMTFunction() {
	super();
	this.id = null;
	this.domainSorts = null;
	this.imageSort = null;
    }

    public SMTFunction(String id, List<SMTSort> domainSorts, SMTSort imageSort) {
	super();
	this.id = Util.processName(id);
	this.domainSorts = domainSorts;
	this.imageSort = imageSort;
    }

    public SMTFunction(String id, SMTSort argSort1, SMTSort argSort2, SMTSort imageSort) {
	super();
	this.id = Util.processName(id);
	List<SMTSort> domainSorts= new LinkedList<SMTSort>();
	domainSorts.add(argSort1);
	domainSorts.add(argSort2);
	this.domainSorts = domainSorts;
	this.imageSort = imageSort;
    }

    public SMTSort getImageSort() {
	return imageSort;
    }

    public void setImageSort(SMTSort imageSort) {
	this.imageSort = imageSort;
    }

    public String getId() {
	return id;
    }

    public void setId(String id) {
	this.id = id;
    }

    public String processString(String id){
	//is symbol already quoted?
	if(id.startsWith("|") && id.endsWith("|")){
	    return id;
	}

	id = id.replace("::", ".");
	id = id.replace("<", "");
	id = id.replace(">", "");
	id = id.replace("$", "");
	id = id.replace("store", "store_");


	//do i need to quote symbol?
	boolean quote = id.contains(":") ||
		id.contains("[") ||
		id.contains("]") ||
		id.contains("(") ||
		id.contains(")");

	if(quote){
	    return "|"+id+"|";
	}
	else{
	    return id;
	}
    }



    /**
     * @return the domainSorts
     */
    public List<SMTSort> getDomainSorts() {
	return domainSorts;
    }

    /**
     * @param domainSorts the domainSorts to set
     */
    public void setDomainSorts(List<SMTSort> domainSorts) {
	this.domainSorts = domainSorts;
    }

    @Override
    public boolean equals (Object obj) {	
	if (obj == null)
	    return false;

	if (this == obj)
	    return true;

	if (!(obj instanceof SMTFunction)) 
	    return false;
	SMTFunction f = (SMTFunction) obj;

	if (!this.id.equals(f.id))
	    return false;

	if (this.domainSorts.size() != f.domainSorts.size())
	    return false;

	for (int i = 0; i < this.domainSorts.size(); i++) {
	    if (!this.domainSorts.get(i).equals(f.domainSorts.get(i)))
		return false;
	}
	return true;
    }

    //	public boolean equals (Function f) {
    //		if (f == null)
    //			return false;
    //		
    //		if (f == this)
    //			return true;
    //		
    //		if (!this.id.equals(f.id))
    //			return false;
    //		
    //		if (this.domainSorts.size() != f.domainSorts.size())
    //			return false;
    //		
    //		for (int i = 0; i < this.domainSorts.size(); i++) {
    //			if (!this.domainSorts.get(i).equals(f.domainSorts.get(i)))
    //				return false;
    //		}
    //		return true;
    //	}

    @Override
    public int hashCode() {
	int ret = id.hashCode();
	int base = 10;
	int i = 1;

	for (SMTSort sort : domainSorts) {
	    ret = ret + sort.getId().hashCode() * base^i;
	    i++;
	}

	return ret;
    }

    public String toString () {
	StringBuffer buff = new StringBuffer();
		
	buff.append("(declare-fun "+id+" "+"(");
	//		if (domainSorts == null) return "domainSorts is null";
	for (SMTSort s : domainSorts) {
	    buff.append(s.getTopLevel().getId()+" ");
	}
	buff.append(")"+" "+imageSort.getTopLevel().getId()+")");

	return buff.toString();

    }










}