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

package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.event.ISEDAnnotationLinkListener;
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
 * <li>{@link ISEDBranchStatement} (branch statement, e.g. {@code if(x >= 0)})</li>
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
    * Checks if children are available.
    * @return {@code true} children are available, {@code false} children are not available.
    * @throws DebugException Occurred Exception
    */
   public boolean hasChildren() throws DebugException;
   
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
   
   /**
    * Adds the given {@link ISEDAnnotationLink} to this node.
    * @param link The {@link ISEDAnnotationLink} to add.
    */
   public void addAnnotationLink(ISEDAnnotationLink link);
   
   /**
    * Removes the given {@link ISEDAnnotationLink} from this node.
    * @param link The {@link ISEDAnnotationLink} to remove.
    */
   public void removeAnnotationLink(ISEDAnnotationLink link);
   
   /**
    * Returns all contained {@link ISEDAnnotationLink}s.
    * @return All contained {@link ISEDAnnotationLink}s.
    */
   public ISEDAnnotationLink[] getAnnotationLinks();
   
   /**
    * Returns all contained {@link ISEDAnnotationLink}s of the given {@link ISEDAnnotationType}.
    * @param type The {@link ISEDAnnotationType}.
    * @return All contained {@link ISEDAnnotationLink}s of the given {@link ISEDAnnotationType}
    */
   public ISEDAnnotationLink[] getAnnotationLinks(ISEDAnnotationType type);
   
   /**
    * Returns all {@link ISEDAnnotation} referenced by {@link ISEDAnnotationLink}s
    * in the order they are defined in the {@link ISEDDebugTarget}.
    * @return The used {@link ISEDAnnotation}s.
    */
   public ISEDAnnotation[] computeUsedAnnotations();
   
   /**
    * Checks if the given {@link ISEDAnnotationLink} is contained in this node.
    * @param link The {@link ISEDAnnotationLink} to check.
    * @return {@code true} the {@link ISEDAnnotationLink} is contained in this node, {@code false} the {@link ISEDAnnotationLink} is not contained.
    */
   public boolean containsAnnotationLink(ISEDAnnotationLink link);
   
   /**
    * Adds the given {@link ISEDAnnotationLinkListener}.
    * @param l The {@link ISEDAnnotationLinkListener} to add.
    */
   public void addAnnotationLinkListener(ISEDAnnotationLinkListener l);
   
   /**
    * Removes the given {@link ISEDAnnotationLinkListener}.
    * @param l The {@link ISEDAnnotationLinkListener} to remove.
    */
   public void removeAnnotationLinkListener(ISEDAnnotationLinkListener l);
   
   /**
    * Returns all {@link IBreakpoint}s which are fulfilled in this {@link ISEDDebugNode}.
    * @return The fulfilled {@link IBreakpoint}s in this {@link ISEDDebugNode}.
    */
   public IBreakpoint[] computeHitBreakpoints() throws DebugException;
   
   /**
    * Checks if constraints are considered at this symbolic execution tree node.
    * @return {@code true} constraints available, {@code false} constraints are not available.
    * @throws DebugException Occurred Exception.
    */
   public boolean hasConstraints() throws DebugException;
   
   /**
    * Returns all constraints which are considered at this symbolic execution tree node.
    * @return All constraints which are considered at this symbolic execution tree node.
    * @throws DebugException Occurred Exception.
    */
   public ISEDConstraint[] getConstraints() throws DebugException;
   
   /**
    * Returns the conditions under which an {@link ISEDGroupable} {@link ISEDDebugNode} is completed by this {@link ISEDDebugNode}.
    * <p>
    * The conditions are ordered by the occurrence in the tree. 
    * This means that the node at the second index is a parent or grand parent of the node at the first index and so on.
    * @return The conditions under which an {@link ISEDGroupable} {@link ISEDDebugNode} is completed by this {@link ISEDDebugNode}.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDBranchCondition[] getGroupStartConditions() throws DebugException;
   
   /**
    * Returns the inner most visible group start condition.
    * @return The inner most visible group start condition or {@code null} if not available.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDBranchCondition getInnerMostVisibleGroupStartCondition() throws DebugException;
   
   /**
    * Returns the condition under which the given {@link ISEDDebugNode} is completed by this {@link ISEDDebugNode}.
    * @return The condition under which the given {@link ISEDDebugNode} is completed by this {@link ISEDDebugNode}.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDBranchCondition getGroupStartCondition(ISEDDebugNode startNode) throws DebugException;
}