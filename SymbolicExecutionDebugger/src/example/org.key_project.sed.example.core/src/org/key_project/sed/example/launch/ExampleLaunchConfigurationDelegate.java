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
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.model.impl.AbstractSEDDebugNode;
import org.key_project.sed.core.model.impl.AbstractSEDValue;
import org.key_project.sed.core.model.impl.AbstractSEDVariable;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEDMemoryStatement;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;
import org.key_project.sed.core.model.memory.SEDMemoryThread;
import org.key_project.sed.core.model.memory.SEDMemoryValue;
import org.key_project.sed.core.model.memory.SEDMemoryVariable;

/**
 * A {@link LaunchConfigurationDelegate} is responsible to start the symbolic 
 * execution engine represented by an {@link ISEDDebugTarget}. Also the initial 
 * symbolic execution tree needs to be constructed which may consists only of a 
 * single {@link ISEDThread} that is the root of a symbolic execution tree.
 * <p>
 * The symbolic execution tree is represented by {@link ISEDDebugNode}s and 
 * its sub types. Each symbolic execution engine has to implement these 
 * interfaces to represent the results from the symbolic execution engine. It is 
 * recommended to subclass from the abstract classes like 
 * {@link AbstractSEDDebugNode}.
 * <p>
 * The symbolic state of each {@link ISEDDebugNode} is represented by multiple 
 * {@link ISEDVariable} and its {@link ISEDValue}. It is recommended to 
 * subclass from {@link AbstractSEDVariable} and {@link AbstractSEDValue}.
 * <p>
 * If the symbolic execution engine is run in a separate process an 
 * {@link IProcess} might be used.
 * <p>
 * The {@link ISEDDebugTarget} as sub type of {@link IStep} is responsible to 
 * control execution. It is good practice to delegate requests to the contained 
 * {@link ISEDThread}s.
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
       ISEDDebugTarget target = createTarget(launch);
       launch.addDebugTarget(target);
    }
    
    /**
     * Constructs the initial symbolic execution tree which is a fixed example.
     * @param launch The parent {@link ILaunch}.
     * @return The created {@link ISEDDebugTarget}.
     */
    private ISEDDebugTarget createTarget(ILaunch launch) {
       // Target
       SEDMemoryDebugTarget target = new SEDMemoryDebugTarget(launch, false);
       target.setName("this.add(MyInteger)");
       target.setModelIdentifier("org.key_project.sed.example.core");
       // Thread
       SEDMemoryThread thread = new SEDMemoryThread(target, false);
       thread.setName("<start>");
       thread.setPathCondition("true");
       target.addSymbolicThread(thread);
       // Method call
       SEDMemoryMethodCall call = new SEDMemoryMethodCall(target, thread, thread);
       call.setName("<call add(other)>");
       call.setPathCondition("true");
       call.setGroupable(true);
       thread.addChild(call);
       // Statement
       SEDMemoryStatement statement = new SEDMemoryStatement(target, call, thread);
       statement.setName("this.value += other.value;");
       statement.setPathCondition("true");
       statement.setCallStack(createCallStack(call));
       call.addChild(statement);
       
       // Not Null Branch Condition
       SEDMemoryBranchCondition notNullBC = new SEDMemoryBranchCondition(target, statement, thread);
       notNullBC.setName("other != null");
       notNullBC.setPathCondition("other != null");
       notNullBC.setCallStack(createCallStack(call));
       statement.addChild(notNullBC);
       // Method return
       SEDMemoryMethodReturn normalReturn = new SEDMemoryMethodReturn(target, notNullBC, thread);
       normalReturn.setName("<return of this.add(other)>");
       normalReturn.setPathCondition("other != null");
       normalReturn.setCallStack(createCallStack(call));
       notNullBC.addChild(normalReturn);
       // Method return condition
       SEDMemoryBranchCondition notNullMethodReturnBC = new SEDMemoryBranchCondition(target, call, thread);
       notNullMethodReturnBC.setName("other != null");
       notNullMethodReturnBC.setPathCondition("other != null");
       notNullMethodReturnBC.addChild(normalReturn);
       notNullMethodReturnBC.setCallStack(createCallStack(call));
       call.addMethodReturnCondition(notNullMethodReturnBC);
       call.addGroupEndCondition(notNullMethodReturnBC);
       normalReturn.setMethodReturnCondition(notNullMethodReturnBC);
       normalReturn.addGroupStartCondition(notNullMethodReturnBC);
       // Normal termination
       SEDMemoryTermination termination = new SEDMemoryTermination(target, normalReturn, thread, true);
       termination.setName("<end>");
       termination.setPathCondition("other != null");
       normalReturn.addChild(termination);
       
       // Not Null Branch Condition
       SEDMemoryBranchCondition nullBC = new SEDMemoryBranchCondition(target, statement, thread);
       nullBC.setName("other == null");
       nullBC.setPathCondition("other == null");
       nullBC.setCallStack(createCallStack(call));
       statement.addChild(nullBC);
       // Exceptional method return
       SEDMemoryExceptionalMethodReturn exceptionalReturn = new SEDMemoryExceptionalMethodReturn(target, nullBC, thread);
       exceptionalReturn.setName("<throw java.lang.NullPointerException>");
       exceptionalReturn.setPathCondition("other == null");
       exceptionalReturn.setCallStack(createCallStack(call));
       nullBC.addChild(exceptionalReturn);
       // Method return condition
       SEDMemoryBranchCondition nullMethodReturnBC = new SEDMemoryBranchCondition(target, call, thread);
       nullMethodReturnBC.setName("other == null");
       nullMethodReturnBC.setPathCondition("other == null");
       nullMethodReturnBC.addChild(exceptionalReturn);
       nullMethodReturnBC.setCallStack(createCallStack(call));
       call.addMethodReturnCondition(nullMethodReturnBC);
       call.addGroupEndCondition(nullMethodReturnBC);
       exceptionalReturn.setMethodReturnCondition(nullMethodReturnBC);
       exceptionalReturn.addGroupStartCondition(nullMethodReturnBC);
       // Normal termination
       SEDMemoryExceptionalTermination exceptionalTermination = new SEDMemoryExceptionalTermination(target, exceptionalReturn, thread, true);
       exceptionalTermination.setName("<uncaught java.lang.NullPointerException>");
       exceptionalTermination.setPathCondition("other == null");
       exceptionalReturn.addChild(exceptionalTermination);
       
       // May add ISEDVariable with ISEDValue to each ISEDDebugNode
       SEDMemoryVariable variable = new SEDMemoryVariable(target, thread);
       variable.setName("Hello");
       SEDMemoryValue value = new SEDMemoryValue(target, variable);
       value.setValueString("World!");
       variable.setValue(value);
       thread.addVariable(variable);

       // Fill the source model to highlight reached code parts during symbolic execution 
       //target.getSourceModel();

       // Use ISEDAnnotation and ISEDAnnotationLink instances to label an ISEDDebugNode, e.g. with hit breakpoints
       BreakpointAnnotation annotation = new BreakpointAnnotation();
       target.registerAnnotation(annotation);
       BreakpointAnnotationLink link = new BreakpointAnnotationLink(annotation, normalReturn);
       link.setBreakpointName("My Breakpoint");
       annotation.addLink(link);
       
       return target;
    }
    
    /**
     * Creates a call stack for the given {@link ISEDMethodCall}s.
     * @param stack The given {@link ISEDMethodCall}s
     * @return The created call stack.
     */
    private static ISEDMethodCall[] createCallStack(ISEDMethodCall... stack) {
       return stack;
    }
}