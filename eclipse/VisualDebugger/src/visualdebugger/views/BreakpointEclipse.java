package visualdebugger.views;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.jface.text.TextSelection;

import de.uka.ilkd.key.visualdebugger.Breakpoint;
import de.uka.ilkd.key.visualdebugger.SourceElementId;

public class BreakpointEclipse extends Breakpoint {
    TextSelection sel;
    Statement st;
    ICompilationUnit unit;
    IMethod method;
    public BreakpointEclipse(SourceElementId arg0, TextSelection sel, 
            Statement st, ICompilationUnit unit, IMethod method) {
        super(arg0);
        this.method = method;
        this.sel = sel;
        this.st = st;
        this.unit = unit;
    }
    
    public TextSelection getSelection(){
        return sel;
    }
    
    public Statement getStatement(){
        return st;
    }
    
    public ICompilationUnit getCompilationUnit(){
        return unit;
    }
    
    public IMethod getMethod(){
        return method;
    }
    
    public String toString(){
        return super.toString();
    }


}
