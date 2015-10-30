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

package org.key_project.sed.core.test.example.fixed_launch_content;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEBranchStatement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEExceptionalTermination;
import org.key_project.sed.core.model.ISELoopCondition;
import org.key_project.sed.core.model.ISELoopStatement;
import org.key_project.sed.core.model.ISEMethodCall;
import org.key_project.sed.core.model.ISEMethodReturn;
import org.key_project.sed.core.model.ISEStatement;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.memory.SEMemoryBranchCondition;
import org.key_project.sed.core.model.memory.SEMemoryBranchStatement;
import org.key_project.sed.core.model.memory.SEMemoryConstraint;
import org.key_project.sed.core.model.memory.SEMemoryDebugTarget;
import org.key_project.sed.core.model.memory.SEMemoryExceptionalMethodReturn;
import org.key_project.sed.core.model.memory.SEMemoryExceptionalTermination;
import org.key_project.sed.core.model.memory.SEMemoryLoopBodyTermination;
import org.key_project.sed.core.model.memory.SEMemoryLoopCondition;
import org.key_project.sed.core.model.memory.SEMemoryLoopStatement;
import org.key_project.sed.core.model.memory.SEMemoryMethodCall;
import org.key_project.sed.core.model.memory.SEMemoryMethodReturn;
import org.key_project.sed.core.model.memory.SEMemoryStatement;
import org.key_project.sed.core.model.memory.SEMemoryTermination;
import org.key_project.sed.core.model.memory.SEMemoryThread;
import org.key_project.sed.core.model.memory.SEMemoryValue;
import org.key_project.sed.core.model.memory.SEMemoryVariable;

/**
 * <p>
 * This {@link LaunchConfigurationDelegate} is responsible to open
 * a fixed model in the given {@link ILaunch}.
 * </p>
 * <p>
 * The following tree is contained:
 * <pre>
 * Fixed Example Test [Fixed Example] ({@link ILaunch})
 *    Fixed Example Target ({@link ISEDebugTarget})
 *         Fixed Example Thread ({@link ISEThread})
 *            int x = 1; ({@link ISEStatement})
 *               while (x == 1) ({@link ISELoopStatement})
 *                  x == 1 ({@link ISELoopCondition})
 *                     x++; ({@link ISEStatement})
 *                        int y = 2; ({@link ISEStatement})
 *                           int result = (x + y) / z; ({@link ISEStatement})
 *                              z == 0 ({@link ISEBranchCondition})
 *                                 throws DivisionByZeroException() ({@link ISEExceptionalTermination}) 
 *                              z != 0 ({@link ISEBranchCondition})
 *                                 foo(result) ({@link ISEMethodCall})
 *                                    if (result >= 0) ({@link ISEBranchStatement})
 *                                       result < 0 ({@link ISEBranchCondition})
 *                                          return -1 ({@link ISEMethodReturn})
 *                                             <end> ({@link ISETermination})
 *                                       result >= 0 ({@link ISEBranchCondition})
 *                                          return 1 ({@link ISEMethodReturn})
 *                                             <end> ({@link ISETermination})
 *   
 * </pre>
 * </p>
 * @author Martin Hentschel
 */
public class FixedExampleLaunchConfigurationDelegate extends LaunchConfigurationDelegate {
   /**
    * The used model identifier.
    */
   public static final String MODEL_IDENTIFIER = "org.key_project.sed.core.test.example.fixed_launch_content";

   /**
     * {@inheritDoc}
     */
    @Override
    public void launch(final ILaunchConfiguration configuration, 
                       String mode, 
                       ILaunch launch, 
                       IProgressMonitor monitor) throws CoreException {
       SEMemoryDebugTarget target = new SEMemoryDebugTarget(launch, false);
       target.setName("Fixed Example Target");
       target.setModelIdentifier(MODEL_IDENTIFIER);
       launch.addDebugTarget(target);
       
       SEMemoryThread thread = new SEMemoryThread(target, false);
       thread.setName("Fixed Example Thread");
       thread.setPathCondition("pc1");
       thread.addConstraint(new SEMemoryConstraint(target, "Thread's Constraint"));
       target.addSymbolicThread(thread);
       
       SEMemoryStatement s1 = new SEMemoryStatement(target, thread, thread);
       s1.setName("int x = 1;");
       s1.setPathCondition("pc2");
       s1.setLineNumber(-1);
       s1.setCharStart(3);
       s1.setCharEnd(5);
       s1.addConstraint(new SEMemoryConstraint(target, "int x = 1 Constraint"));
       thread.addChild(s1);
       
       SEMemoryConstraint s1Constarint1 = new SEMemoryConstraint(target, "s1Constarint1");
       s1.addConstraint(s1Constarint1);
       SEMemoryConstraint s1Constarint2 = new SEMemoryConstraint(target, "s1Constarint2");
       s1.addConstraint(s1Constarint2);
       SEMemoryConstraint s1Constarint3 = new SEMemoryConstraint(target, "s1Constarint3");
       s1.addConstraint(s1Constarint3);
       
       SEMemoryVariable s1var1 = new SEMemoryVariable(target, s1);
       s1var1.setName("var1");
       s1var1.setReferenceTypeName("var1type");
       SEMemoryValue s1var1value = new SEMemoryValue(target, s1var1);
       s1var1value.setReferenceTypeName("s1var1valueType");
       s1var1value.setValueString("s1var1value");
       s1var1value.addRelevantConstraint(s1Constarint1);
       s1var1.setValue(s1var1value);
       s1.addVariable(s1var1);
       
       SEMemoryVariable s1var2 = new SEMemoryVariable(target, s1);
       s1var2.setName("var2");
       s1var2.setReferenceTypeName("var2type");
       SEMemoryValue s1var2value = new SEMemoryValue(target, s1var2);
       s1var2value.setReferenceTypeName("s1var2valueType");
       s1var2value.setValueString("s1var2value");
       s1var2value.addRelevantConstraint(s1Constarint2);
       s1var2.setValue(s1var2value);
       s1.addVariable(s1var2);
       
       SEMemoryLoopStatement ln = new SEMemoryLoopStatement(target, s1, thread);
       ln.setName("while (x == 1)");
       ln.setPathCondition("pc3");
       ln.setGroupable(false);
       s1.addChild(ln);
       
       SEMemoryLoopCondition lc = new SEMemoryLoopCondition(target, ln, thread);
       lc.setName("x == 1");
       lc.setPathCondition("pc4");
       ln.addChild(lc);
       
       SEMemoryStatement ls = new SEMemoryStatement(target, lc, thread);
       ls.setName("x++;");
       ls.setPathCondition("pc5");
       lc.addChild(ls);
       
       SEMemoryStatement s2 = new SEMemoryStatement(target, ls, thread);
       s2.setName("int y = 2;");
       s2.setPathCondition("pc6");
       ls.addChild(s2);
       
       SEMemoryStatement s3 = new SEMemoryStatement(target, s2, thread);
       s3.setName("int result = (x + y) / z;");
       s3.setPathCondition("pc7");
       s2.addChild(s3);
       
       SEMemoryBranchCondition bzero = new SEMemoryBranchCondition(target, s3, thread);
       bzero.setName("z == 0");
       bzero.setPathCondition("pc8");
       s3.addChild(bzero);
       
       SEMemoryExceptionalTermination et = new SEMemoryExceptionalTermination(target, bzero, thread, true);
       et.setName("throws DivisionByZeroException()");
       et.setPathCondition("pc9");
       bzero.addChild(et);
       thread.addTermination(et);
       
       SEMemoryBranchCondition bnotzero = new SEMemoryBranchCondition(target, s3, thread);
       bnotzero.setName("z != 0");
       bnotzero.setPathCondition("pc10");
       s3.addChild(bnotzero);

       SEMemoryMethodCall call = new SEMemoryMethodCall(target, bnotzero, thread);
       call.setName("foo(result)");
       call.setPathCondition("pc11");
       call.setGroupable(true);
       bnotzero.addChild(call);

       SEMemoryBranchStatement branch = new SEMemoryBranchStatement(target, call, thread);
       branch.setName("if (result >= 0)");
       branch.setPathCondition("pc12");
       branch.setCallStack(new ISENode[] {call});
       call.addChild(branch);
       
       SEMemoryBranchCondition bnegative = new SEMemoryBranchCondition(target, branch, thread);
       bnegative.setName("result < 0");
       bnegative.setPathCondition("pc13");
       bnegative.setCallStack(new ISENode[] {call});
       branch.addChild(bnegative);
       
       SEMemoryMethodReturn returnNegative = new SEMemoryMethodReturn(target, bnegative, thread);
       returnNegative.setName("return -1");
       returnNegative.setPathCondition("pc14");
       returnNegative.setCallStack(new ISENode[] {call});
       SEMemoryBranchCondition returnCondition = new SEMemoryBranchCondition(target, call, thread);
       returnCondition.setName("A Return Condition");
       returnCondition.addChild(returnNegative);
       returnNegative.addGroupStartCondition(returnCondition);
       call.addMethodReturnCondition(returnCondition);
       call.addGroupEndCondition(returnCondition);
       returnNegative.setMethodReturnCondition(returnCondition);
       bnegative.addChild(returnNegative);
       
       SEMemoryVariable negativeCallVar = new SEMemoryVariable(target, et);
       negativeCallVar.setName("negativeCallVar");
       returnNegative.addCallStateVariable(negativeCallVar);
       SEMemoryValue negativeCallVarValue = new SEMemoryValue(target, negativeCallVar);
       negativeCallVarValue.setValueString("negativeCallVarValue");
       negativeCallVar.setValue(negativeCallVarValue);
       SEMemoryVariable negativeCallVarChild = new SEMemoryVariable(target, et);
       negativeCallVarChild.setName("negativeCallVarChild");
       negativeCallVarValue.addVariable(negativeCallVarChild);
       SEMemoryValue negativeCallVarChildValue = new SEMemoryValue(target, negativeCallVarChild);
       negativeCallVarChildValue.setValueString("negativeCallVarChildValue");
       negativeCallVarChild.setValue(negativeCallVarChildValue);
       
       SEMemoryTermination terminationNegative = new SEMemoryTermination(target, returnNegative, thread, true);
       terminationNegative.setName("<end>");
       terminationNegative.setPathCondition("pc15");
       returnNegative.addChild(terminationNegative);
       thread.addTermination(terminationNegative);
       
       SEMemoryBranchCondition bpositive = new SEMemoryBranchCondition(target, branch, thread);
       bpositive.setName("result >= 0");
       bpositive.setPathCondition("pc16");
       bpositive.setCallStack(new ISENode[] {call});
       branch.addChild(bpositive);
       
       SEMemoryExceptionalMethodReturn returnPositive = new SEMemoryExceptionalMethodReturn(target, bpositive, thread);
       returnPositive.setName("return 1");
       returnPositive.setPathCondition("pc17");
       returnPositive.setCallStack(new ISENode[] {call});
       bpositive.addChild(returnPositive);
       
       SEMemoryVariable returnPositiveVar1 = new SEMemoryVariable(target, returnPositive);
       returnPositiveVar1.setName("returnPositiveVar1");
       returnPositiveVar1.setReferenceTypeName("returnPositiveVar1type");
       SEMemoryValue returnPositiveVar1value = new SEMemoryValue(target, returnPositiveVar1);
       returnPositiveVar1value.setAllocated(true);
       returnPositiveVar1value.setReferenceTypeName("returnPositiveVar1valueType");
       returnPositiveVar1value.setValueString("returnPositiveVar1value");
       returnPositiveVar1.setValue(returnPositiveVar1value);
       returnPositive.addVariable(returnPositiveVar1);
       
       SEMemoryVariable returnPositiveVar1_1 = new SEMemoryVariable(target, returnPositive);
       returnPositiveVar1_1.setName("returnPositiveVar1_1");
       returnPositiveVar1_1.setReferenceTypeName("returnPositiveVar1_1type");
       SEMemoryValue returnPositiveVar1_1value = new SEMemoryValue(target, returnPositiveVar1_1);
       returnPositiveVar1_1value.setAllocated(true);
       returnPositiveVar1_1value.setReferenceTypeName("returnPositiveVar1_1valueType");
       returnPositiveVar1_1value.setValueString("returnPositiveVar1_1value");
       returnPositiveVar1_1.setValue(returnPositiveVar1_1value);
       returnPositive.addVariable(returnPositiveVar1_1);
       
       SEMemoryVariable returnPositiveVar2 = new SEMemoryVariable(target, returnPositive);
       returnPositiveVar2.setName("returnPositiveVar2");
       returnPositiveVar2.setReferenceTypeName("returnPositiveVar2type");
       SEMemoryValue returnPositiveVar2value = new SEMemoryValue(target, returnPositiveVar2);
       returnPositiveVar2value.setAllocated(true);
       returnPositiveVar2value.setReferenceTypeName("returnPositiveVar2valueType");
       returnPositiveVar2value.setValueString("returnPositiveVar2value");
       returnPositiveVar2.setValue(returnPositiveVar2value);
       returnPositive.addVariable(returnPositiveVar2);
       
       SEMemoryLoopBodyTermination terminationPositive = new SEMemoryLoopBodyTermination(target, returnPositive, thread, true);
       terminationPositive.setName("<loop body end>");
       terminationPositive.setPathCondition("pc18");
       returnPositive.addChild(terminationPositive);
       thread.addTermination(terminationPositive);
    }
}