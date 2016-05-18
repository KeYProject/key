/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.example.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IStep;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotation;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotationLink;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.ISEValue;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.model.impl.AbstractSENode;
import org.key_project.sed.core.model.impl.AbstractSEValue;
import org.key_project.sed.core.model.impl.AbstractSEVariable;
import org.key_project.sed.core.model.memory.SEMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEMemoryExceptionalMethodReturn;
import org.key_project.sed.core.model.memory.SEMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEMemoryStatement;
import org.key_project.sed.core.model.memory.SEMemoryTermination;
import org.key_project.sed.core.model.memory.SEMemoryThread;
import org.key_project.sed.core.model.memory.SEMemoryValue;
import org.key_project.sed.core.model.memory.SEMemoryVariable;

/**
 * A {@link LaunchConfigurationDelegate} is responsible to start the symbolic 
 * execution engine represented by an {@link ISEDebugTarget}. Also the initial 
 * symbolic execution tree needs to be constructed which may consists only of a 
 * single {@link ISEThread} that is the root of a symbolic execution tree.
 * <p>
 * The symbolic execution tree is represented by {@link ISENode}s and 
 * its sub types. Each symbolic execution engine has to implement these 
 * interfaces to represent the results from the symbolic execution engine. It is 
 * recommended to subclass from the abstract classes like 
 * {@link AbstractSENode}.
 * <p>
 * The symbolic state of each {@link ISENode} is represented by multiple 
 * {@link ISEVariable} and its {@link ISEValue}. It is recommended to 
 * subclass from {@link AbstractSEVariable} and {@link AbstractSEValue}.
 * <p>
 * If the symbolic execution engine is run in a separate process an 
 * {@link IProcess} might be used.
 * <p>
 * The {@link ISEDebugTarget} as sub type of {@link IStep} is responsible to 
 * control execution. It is good practice to delegate requests to the contained 
 * {@link ISEThread}s.
 * @author Martin Hentschel
 */
public class ExampleLaunchConfigurationDelegate extends LaunchConfigurationDelegate {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(final ILaunchConfiguration configuration, 
                       String mode, 
                       ILaunch launch, 
                       IProgressMonitor monitor) throws CoreException {
       // May launch the symbolic execution engine in a different process.
       //IProcess process = ..
       //launch.addProcess(process);
      
       // Construct the initial symbolic execution tree.
       ISEDebugTarget target = createTarget(launch);
       launch.addDebugTarget(target);
    }
    
    /**
     * Constructs the initial symbolic execution tree which is a fixed example.
     * @param launch The parent {@link ILaunch}.
     * @return The created {@link ISEDebugTarget}.
     */
    private ISEDebugTarget createTarget(ILaunch launch) {
       // Target
       SEMemoryDebugTarget target = new SEMemoryDebugTarget(launch, false);
       target.setName("this.add(MyInteger)");
       target.setModelIdentifier("org.key_project.sed.example.core");
       // Thread
       SEMemoryThread thread = new SEMemoryThread(target, false);
       thread.setName("Main");
       target.addSymbolicThread(thread);
       // Method call
       SEMemoryStatement main28 = new SEMemoryStatement(target, thread, thread);
       main28.setName("Object x = new Object();");
       thread.addChild(main28);
       // Statement
       SEMemoryStatement main29 = createStatement(main28, "ClassicDeadlock cd = new ClassicDeadlock();");
       SEMemoryStatement main31 = createStatement(main29, "cd.BuldNetworks(3, x, x)");
       SEMemoryStatement main13 = createStatement(main31, "if (n === 0)");
       SEMemoryStatement main23 = createStatement(main13, "todo.start()");
       SEMemoryStatement main24 = createStatement(main23, "this.BuildNetwork(n-1)");
       SEMemoryStatement main13again = createStatement(main24, "if (n === 0)");
       SEMemoryStatement main14 = createStatement(main13again, "this.TakeLocks(x, y)");
       SEMemoryStatement main6 = createStatement(main14, "synchronized(150)");
       SEMemoryStatement main7 = createStatement(main6, "synchronized(163)");

       
       // Thread
       SEMemoryThread thread2 = new SEMemoryThread(target, false);
       thread2.setName("toto");
       target.addSymbolicThread(thread2);
       // Method call
       SEMemoryStatement main20 = new SEMemoryStatement(target, thread2, thread2);
       main20.setName("TakeLocks(x, y)");
       thread2.addChild(main20);
       // Statement
       main6 = createStatement(main20, "synchronized(163)");
       main7 = createStatement(main6, "synchronized(150)");
       
       //       
//       // Not Null Branch Condition
//       SEMemoryBranchCondition notNullBC = new SEMemoryBranchCondition(target, statement, thread);
//       notNullBC.setName("other != null");
//       notNullBC.setPathCondition("other != null");
//       notNullBC.setCallStack(createCallStack(call));
//       statement.addChild(notNullBC);
//       // Method return
//       SEMemoryMethodReturn normalReturn = new SEMemoryMethodReturn(target, notNullBC, thread);
//       normalReturn.setName("<return of this.add(other)>");
//       normalReturn.setPathCondition("other != null");
//       normalReturn.setCallStack(createCallStack(call));
//       notNullBC.addChild(normalReturn);
//       // Method return condition
//       SEMemoryBranchCondition notNullMethodReturnBC = new SEMemoryBranchCondition(target, call, thread);
//       notNullMethodReturnBC.setName("other != null");
//       notNullMethodReturnBC.setPathCondition("other != null");
//       notNullMethodReturnBC.addChild(normalReturn);
//       notNullMethodReturnBC.setCallStack(createCallStack(call));
//       call.addMethodReturnCondition(notNullMethodReturnBC);
//       call.addGroupEndCondition(notNullMethodReturnBC);
//       normalReturn.setMethodReturnCondition(notNullMethodReturnBC);
//       normalReturn.addGroupStartCondition(notNullMethodReturnBC);
//       // Normal termination
//       SEMemoryTermination termination = new SEMemoryTermination(target, normalReturn, thread, true);
//       termination.setName("<end>");
//       termination.setPathCondition("other != null");
//       normalReturn.addChild(termination);
//       
//       // Not Null Branch Condition
//       SEMemoryBranchCondition nullBC = new SEMemoryBranchCondition(target, statement, thread);
//       nullBC.setName("other == null");
//       nullBC.setPathCondition("other == null");
//       nullBC.setCallStack(createCallStack(call));
//       statement.addChild(nullBC);
//       // Exceptional method return
//       SEMemoryExceptionalMethodReturn exceptionalReturn = new SEMemoryExceptionalMethodReturn(target, nullBC, thread);
//       exceptionalReturn.setName("<throw java.lang.NullPointerException>");
//       exceptionalReturn.setPathCondition("other == null");
//       exceptionalReturn.setCallStack(createCallStack(call));
//       nullBC.addChild(exceptionalReturn);
//       // Method return condition
//       SEMemoryBranchCondition nullMethodReturnBC = new SEMemoryBranchCondition(target, call, thread);
//       nullMethodReturnBC.setName("other == null");
//       nullMethodReturnBC.setPathCondition("other == null");
//       nullMethodReturnBC.addChild(exceptionalReturn);
//       nullMethodReturnBC.setCallStack(createCallStack(call));
//       call.addMethodReturnCondition(nullMethodReturnBC);
//       call.addGroupEndCondition(nullMethodReturnBC);
//       exceptionalReturn.setMethodReturnCondition(nullMethodReturnBC);
//       exceptionalReturn.addGroupStartCondition(nullMethodReturnBC);
//       // Normal termination
//       SEMemoryExceptionalTermination exceptionalTermination = new SEMemoryExceptionalTermination(target, exceptionalReturn, thread, true);
//       exceptionalTermination.setName("<uncaught java.lang.NullPointerException>");
//       exceptionalTermination.setPathCondition("other == null");
//       exceptionalReturn.addChild(exceptionalTermination);
//       
//       // May add ISEDVariable with ISEDValue to each ISEDDebugNode
//       SEMemoryVariable variable = new SEMemoryVariable(target, thread);
//       variable.setName("Hello");
//       SEMemoryValue value = new SEMemoryValue(target, variable);
//       value.setValueString("World!");
//       variable.setValue(value);
//       thread.addVariable(variable);
//
//       // Fill the source model to highlight reached code parts during symbolic execution 
//       //target.getSourceModel();
//
//       // Use ISEDAnnotation and ISEDAnnotationLink instances to label an ISEDDebugNode, e.g. with hit breakpoints
//       BreakpointAnnotation annotation = new BreakpointAnnotation();
//       target.registerAnnotation(annotation);
//       BreakpointAnnotationLink link = new BreakpointAnnotationLink(annotation, normalReturn);
//       link.setBreakpointName("My Breakpoint");
//       annotation.addLink(link);
       
       return target;
    }
    
    protected SEMemoryStatement createStatement(SEMemoryStatement parent, String name) {
       SEMemoryStatement main31 = new SEMemoryStatement(parent.getDebugTarget(), parent, parent.getThread());
       main31.setName(name);
       parent.addChild(main31);
       return main31; 
    }
    
    /**
     * Creates a call stack for the given {@link ISEMethodCall}s.
     * @param stack The given {@link ISEMethodCall}s
     * @return The created call stack.
     */
    private static ISEMethodCall[] createCallStack(ISEMethodCall... stack) {
       return stack;
    }
}