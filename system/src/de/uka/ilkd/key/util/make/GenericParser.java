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

package de.uka.ilkd.key.util.make;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.util.LinkedHashSet;
import java.util.Set;

public class GenericParser {

    /** .gjava directory */
    public static String genericPath="./de/uka/ilkd/key/collection/";

    /** The generated makefile will write the names of generated
     * java files into this file */
    public static String compileListFileName;

    /** the existing java classes with its dividers.
     * The value of genClass[i].length has to be equal to 
     * the amount of templates.
     */
    public static String[][] genClass={ 
	{"HashMapFrom","To"},
	{"ListOf"},
	{"SLListOf"},
	{"SetOf"},
	{"SetAsListOf"},
	{"IteratorOf"},
	{"MapFrom","To"},
	{"EntryOf","And"},
	{"MapAsListFrom","To"},
	{"ArrayOf","Ext","In"},
	{"VectorOf"},
	{"HeapOf"}, {"LeftistHeapOf"},
	{"SimpleStackOf"}
    };

    /** dependencies as the .gjava-file (same position as above)
     * if you write <name>%<nr> the %<nr> will be replaced with the nr-th
     * template (nr<=9) e.g. IteratorOf%1 becomes IteratorOfString if it is 
     * a dependency of SetOfString
     */
    public static String[][] dep={
	{"HashMapFrom<S>To<T>.gjava","IteratorOf%1.java"},//,"IteratorOf%2.java"},
	{"ListOf<T>.gjava","IteratorOf%1.java"},
	{"SLListOf<T>.gjava","ListOf%1.java"},	
	{"SetOf<T>.gjava"},
	{"SetAsListOf<T>.gjava","SetOf%1.java","SLListOf%1.java"},
	{"IteratorOf<T>.gjava"},
	{"MapFrom<S>To<T>.gjava"},
	{"EntryOf<S>And<T>.gjava"},
	{"MapAsListFrom<S>To<T>.gjava","MapFrom%1To%2.java",
	 "SLListOfEntryOf%1And%2.java", 
	 "EntryOf%1And%2.java",//"SLListOf%1.java","SLListOf%2.java", disabled 
	                       // because of distributed packages
	 "IteratorOfEntryOf%1And%2.java"},
	{"ArrayOf<S>.gjava"},
	{"VectorOf<T>.gjava","IteratorOf%1.java"},
	{"HeapOf<T>.gjava","IteratorOf%1.java"},
	{"LeftistHeapOf<T>.gjava","HeapOf%1.java"},
	{"SimpleStackOf<T>.gjava","IteratorOf%1.java"}
    };
    
    public static String generatedSrcPath;

    // Hashes rules that have been created
    private static Set<String> ruleSet=new LinkedHashSet<String>();


    // STATIC METHODS

    public static String parse(String parseStr) {
 	GenericParser gp=new GenericParser();
	String path=getPath(parseStr);	
	if (path.equals("")) {
	    path="./";
	}

	String className=getClassName(parseStr);
 	Template top=gp.start(className); 	
	String[] depend=dependencies(top,path);
	String makeStr=createMakefileEntry(top,path);	

	for (int i=1;i<depend.length;i++) {// create Makefile entry for 
	    // dependencies (generic ones only)
	    makeStr+=parse(depend[i]);
	}

	// if this generic build up on other generic file
	// create a makefile entry for them too
	for (int i=0;i<top.size();i++) {
	    makeStr+=parse(path+top.template(i).toString());
	}
	if (!makeStr.equals("")) {
	    System.out.print(".");
	}
	return makeStr;
    }

   // MAIN - MAIN - MAIN - MAIN - MAIN - MAIN 
    /** run parser and create makestr */
    public static void main(String[] args) {
	generatedSrcPath = args[0];
	if (!generatedSrcPath.endsWith("/")) {
	    generatedSrcPath = generatedSrcPath+"/";
	}
	File genericMakefile = new File(args[1]);
	compileListFileName = args[2];
	ruleSet = new MakefileReader(genericMakefile).getRules();
	ByteArrayOutputStream bos = new ByteArrayOutputStream();
 	try {
	    if (genericMakefile.exists()) {
		FileInputStream fr = new FileInputStream(genericMakefile);
		int chr = fr.read();
		while (chr != -1) {
		    bos.write(chr);
		    chr = fr.read();
		}
		bos.write((byte)'\n');
	        fr.close();
	    }
	    if (args.length > 1) {
		System.out.print("[creating Makefile entries ");
	    }
	    for (int i = 3; i < args.length; i++) {
		bos.write(parse(args[i]).getBytes());
	    }
 	    FileOutputStream fw = new FileOutputStream(genericMakefile);
	    bos.writeTo(fw);
 	    fw.close();
 	} catch (Exception e) {
 	    System.out.println("File operation failed: "+e);
 	}	
	System.out.println(" READY]");
    }

    /** creates a single Makefile entry */
    public static String createMakefileEntry(Template t, String path) { 
	if (t.id()==-1) { // no generic file
	    return "";
	} 
	// first get rule
	String tmpPath = path+t.toString()+".java";
 	String makeStr=tmpPath+": "+generatedSrcPath+tmpPath+";\n";
 	makeStr+=generatedSrcPath+path+makeRule(t.toString(),dependencies(t,path));
	if (!ruleSet.contains(path+t.toString()+".java")) {
	    ruleSet.add(path+t.toString()+".java");
	    // append make generic action
	    makeStr+="\n"+makeAction(t,path)+"\n";
	    // append move name of created .java file to compileListFileName

	    // handle special extension of ArrayOf (delete Ext...)
	    String fileName=t.toString();
	    if (t.id()==matchGenClass("ArrayOf")) {
		fileName=fileName.substring(0,fileName.indexOf("Ext"));
	    }
	    if (path.startsWith("./")) {
		path = path.substring(2);
	    }
	    makeStr+="\t@echo "+generatedSrcPath+path+""+fileName+".java >>" +
		compileListFileName + "\n";
	} else {
	    makeStr="";
	}
	return makeStr;
    }
    
    /** create dependencies */
    public static String[] dependencies(Template t, String path) {
	if (t.id()==-1) {
	    return new String[0];
	}
	String[] deps=new String[dep[t.id()].length];
       	for (int i=0;i<dep[t.id()].length;i++) {
	    deps[i]=(i==0 ? genericPath : path);
	    deps[i]+=replace(dep[t.id()][i],t);
	}
	
	return deps;
    }

    /** create rule */
    public static String makeRule(String pattern, String[] dep) {
	String depStr="";
	for (int i=0;i<dep.length;i++) {
	    depStr+=(i==0 ? "" : generatedSrcPath)+dep[i]+" ";
	}
	
	return pattern+".java"+": "+depStr;
    }

    /** create action */
    public static String makeAction(Template t, String path) {
	StringBuffer action=new StringBuffer("\t@");
	action.append(genericPath+dep[t.id()][0]); // calls .gjava script

	StringBuffer pck=new StringBuffer(path); // the package name
	replaceAll(pck,"/",".");
	if (pck.charAt(pck.length()-1)=='.') {
	    pck.delete(pck.length()-1,pck.length());
	}
	action.append(" "+pck+" "); 
	
	// creates : path/<file>.gjava packagename template1 t2 ...
	for (int i=0;i<t.size();i++) {
	    action.append(" "+t.template(i));
	}

	// adds created .gjava created file to a container 
// 	for (int i=0;i<t.size();i++) {
// 	    action.append(" "+t.template(i)+" ");
// 	}

	// the char < has to be declared as \<
	replaceAll(action,"<","\\<");
	replaceAll(action,">","\\>");	
	
	return action.toString();
    }


    /** gets path */
    public static String getPath(String file) {
	File f=new File(file);
	String path=f.getPath(); // path/<name>.java
	return path.substring(0,path.lastIndexOf('/')+1); // skip  <name>.java
    }

    /** get name of class (filename without suffix) */
    public static String getClassName(String file) {
	File f=new File(file);
	String name=f.getName(); 
	if (name.lastIndexOf('.')>=0) {
	    return name.substring(0,name.lastIndexOf('.')); // skip .java
	} 
	return name;
    }


    /** replace all occurrences of search in sb with repl */
    public static void replaceAll(StringBuffer sb, String search, 
				  String repl) {
	int idx=0;
	int add=0;
	String sbStr=sb.toString();
	while ((idx=sbStr.indexOf(search,idx))!=-1) {
	    int start=idx+add;
	    int end=idx+search.length()+add;
	    end=(end>=sb.length() ? sb.length() : end);
	    sb.replace(start,end,repl);
	    add+=repl.length()-search.length();
	    idx+=add+1;
	}	
    }


    /** replace char at position pos with pos+len in str with replaceStr
     * @param str String to be edited
     * @param pos int the position 
     * @param len int the len of the substring being replaced
     * @param replaceStr the String we put at pos in str 
     */
    public static String replace(String str, int pos, int len, 
				  String replaceStr) { 
	return str.substring(0,pos)+replaceStr+str.substring(pos+len);
    }

    
    /** @param str the String we want to replace %nr
     *  @param tpl the Template 
     *	@return str replace took place
     */
    public static String replace(String str, Template tpl) {
	String replaced=str;
	int occur=0;
	int value=0;
	while ((occur=replaced.indexOf('%'))!=-1) {
	    value=Integer.valueOf(""+replaced.charAt(occur+1)).intValue()-1;	    
	    replaced=replace(replaced,occur,2,tpl.template(value).toString());   
	    occur+=2;
	}
	return replaced;	
    }


    // DYNAMIC PART STARTS HERE

    /** @return number of different generic classes */
    private static int genSize() {
	return genClass.length;
    }

        
    /** @return template that fits for the op-represented type  */
    private static int matchGenClass(String op) {
	int i=0;
	while(i<genSize()) {
	    if (op.startsWith(genClass[i][0])) {
		return i;
	    }
	    i++;
	}
	return -1;
    }

    /** @return String representation of the next expected separator */
    private String nextExpectedSep(Template child) {
	Template tpl=child;
	while (tpl.hasParent() && tpl.nextSep().equals("")) { 
	    // look for next sep
	    tpl=tpl.parent();
	}	
	return tpl.nextSep();
    }
    
    private Template parse(String rest,Template parent) {	
	// rest=A(<SEP>B)
	// extract A
	// split
	// look left side is it generic
	Template top=null;
	Template child=null;
	int childID=matchGenClass(rest);
  	if (childID==-1 && parent==null) { // no generic class at top level
  	    return new Template(childID,
  				"",
  				null);
  	} else
	if (childID==-1) { // A is not generic type lets extract A
	    String sep=nextExpectedSep(parent);
	    if (sep.equals("")) { // case rest=A 
		top=new Template(childID,rest,parent);
	    } else { // case rest=A<SEP>B			
	       	int idx=rest.indexOf(sep);
		top=new Template(childID,
				 rest.substring(0,idx),
				 parent);
	    }
	} else { // A is a generic type
	    top=new Template(childID,genClass[childID][0],parent);
	    // parse A
	    child=parse(rest.substring(genClass[childID][0].length()),
			 top);
	    top.add(child);    
	    // parseB

	    String newRest=rest.substring(top.type().length());
	    for (int i=1;i<top.size();i++) {
		int sepLen=top.sep(top.indexOfSep()-1).length();
		int newRestStartsAtIdx=child.toString().length()+sepLen;
		newRest=newRest.substring(newRestStartsAtIdx);
		if (!newRest.equals("")) {
		    child=parse(newRest,top);	    
		    top.add(child);
		}
		
	    }
	}

	return top;
    }

    private Template start(String str) {
	return parse(str,null);
    }
   
    class Template {
	private int id;
 	private String type;
	private Template parent;
	private Template[] tpl;	
	private int idx;
	private int indexOfSep;
	
	Template() {
 	    id=-1;
	    parent=null;
	    type="";
	    tpl=null;
	    idx=0;
	    indexOfSep=0;
	}

	Template(int id, String type, Template parent) {
	    this();
	    this.id=id;
	    this.type=type;
	    this.parent=parent;
	    tpl=new Template[(id==-1 ? 0 : genClass[id].length)];
	}


	String nextSep() {
	    return sep(indexOfSep());
	}

	int indexOfSep() {
	    return indexOfSep;
	}

	int sep() {
	    return genClass[id].length-1;
	}

	String sep(int i) {
	    if (i<sep()) {
		return genClass[id][i+1];
	    }
	    return "";	    
	}

	Template parent() {
	    return parent;
	}

	boolean hasParent() {
	    return parent!=null;
	}

	void add(Template t) {
	    tpl[idx]=t;
	    indexOfSep++;
	    idx++;
	}

	int size() {
	    return tpl.length;
	}

	int id() {
	    return id;
	}

	Template template(int i) {
	    return tpl[i];
	}

	String type() {
	    return type;
	}

	public String toString() {
	    String str=type();
	    if (size()==0) {
		return str;
	    }	    
	    str+=template(0);
	    for (int i=1;i<size();i++) {
		if (size()>1) {
		    str+=genClass[id()][i];
		}
		str+=template(i);
	    }
	    return str;
	}

    }


}