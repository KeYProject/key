/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDDebugNode;
import org.key_project.sed.core.model.impl.AbstractSEDStackFrameCompatibleDebugNode;

/**
 * A node and his sub interfaces forms the symbolic execution tree for
 * each thread. A node contains the available children.
 * <p>
 * The following concrete nodes are available
 * <ul>
 * <li>{@link ISEDThread} (root node)</li>
 * <li>{@link ISEDStatement} (single statement, e.g. {@code int x =  1 + 2;})</li>
 * <li>{@link ISEDBranchNode} (branch node, e.g. {@code if(x >= 0)})</li>
 * <li>{@link ISEDBranchCondition} (branch condition, e.g. {@code x < 0})</li>
 * <li>{@link ISEDMethodCall} (method call, e.g. {@code foo()})</li>
 * <li>{@link ISEDMethodReturn} (method return, e.g. {@code return 42})</li>
 * <li>{@link ISEDTermination} (termination, e.g. {@code <end>})</li>
 * <li>{@link ISEDExceptionalTermination} (exceptional termination, e.g. {@code <uncaught java.lang.NullPointerException>})</li>
 * </ul>
 * </p>
 * <p>
 * Clients may implement this interface. It should not be directly instantiated.
 * It is recommended to instantiate always one of the provided sub interfaces
 * and to subclass from {@link AbstractSEDDebugNode} or from
 * {@link AbstractSEDStackFrameCompatibleDebugNode} if the sub interface
 * also extends {@link IStackFrame} for compatibility reasons with the
 * Eclipse debug API.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDDebugNode extends ISEDDebugElement {
   /**
    * Returns the contained children.
    * @return
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDDebugNode[] getChildren() throws DebugException;
   
   /**
    * Returns the {@link ISEDThread} in that this {@link ISEDDebugNode} is contained 
    * as child. An {@link ISEDThread} returns itself.
    * @return The {@link ISEDThread}.
    * @throws DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDThread getThread() throws DebugException;
   
   /**
    * Returns the parent in that this node is contained as child.
    * @return The parent {@link ISEDDebugNode} or {@code null} if it is the root of the symbolic execution tree.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDDebugNode getParent() throws DebugException;
   
   /**
    * Returns a human readable name.
    * @return The name of this node.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public String getName() throws DebugException;
   
   /**
    * Returns a human readable node type name.
    * @return The human readable node type.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public String getNodeType() throws DebugException; 
   
   /**
    * Returns a human readable path condition to the current node.
    * @return The human readable path condition to the current node.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public String getPathCondition() throws DebugException;
   
   /**
    * Returns the method call stack.
    * @return The method call stack.
    * @throws DebugException DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDDebugNode[] getCallStack() throws DebugException;
}