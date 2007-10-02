package de.uka.ilkd.key.visualdebugger;

import java.io.File;

/**
 * A source element id identifies an occurrence of a source code element
 * unambigously. In the current implementation an occurrence is identified by 
 * labeling programs (up to now only statement labels are supported). the labelling is
 * performed by inserting a pseudo method call <tt>Debug.sep(id)</tt>
 * before and after each statement. 
 * 
 * An isnatnce of this class refers to exact one such label. 
 */
public class SourceElementId {
    private int id;
    private String className="";
    private boolean isStatement=true;

    private File file;
    private boolean isBoolean=false;
    
    
    public SourceElementId(String cl, int id) {
        this.id = id;
        this.className = cl;

    }
    
    public SourceElementId(String cl, String id,boolean isStatement,boolean isBoolean) {
        this(cl,id);
        this.isStatement = isStatement;
        this.isBoolean   = isBoolean;
    }
    

    public SourceElementId(String id) {
        this("", new Integer(id).intValue());
    }
    
    public SourceElementId(String cl, String id) {
        this(id);
        this.className= cl;

    }

    public int getId() {
        return id;
    }

    public File getFile() {        
        return file;
    }
    
    public String getClassName(){
        return className;
    }

    public boolean equals(Object o) {
        if (o instanceof SourceElementId) {
            SourceElementId id2 = (SourceElementId) o;
            return id == id2.getId();
        }         
        return false;
    }

    public int hashCode(){
        return id;
    }
    
    public String toString(){
        return "Class Name: "+className+" Statement: "+id+" File"+file;
    }

    public boolean isStatement() {
        return isStatement;
    }
    
    public boolean isBoolean() {
        return isBoolean;
    }
    
}
