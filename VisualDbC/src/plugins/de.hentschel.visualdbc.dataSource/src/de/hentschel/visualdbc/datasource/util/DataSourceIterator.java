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

package de.hentschel.visualdbc.datasource.util;

import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * <p>
 * Subclasses of this class can be used to iterate over the containment
 * hierarchy in an {@link IDSConnection}.
 * </p>
 * <p>
 * The iterateOver* methods are used to follow the containment hierarchy.
 * Each element is visited exactly once.
 * </p>
 * <p>
 * The workOn* methods can be overwritten to do something with the current
 * object.
 * </p>
 * @author Martin Hentschel
 */
public class DataSourceIterator {
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverConnection(IDSConnection instance) throws DSException {
      workOnConnection(instance);
      iterateOverContainer(instance);
   }

   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnConnection(IDSConnection instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverPackage(IDSPackage instance) throws DSException {
      workOnPackage(instance);
      iterateOverContainer(instance);
   }

   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverContainer(IDSContainer instance) throws DSException {
      for (IDSPackage childPackage : instance.getPackages()) {
         iterateOverPackage(childPackage);
      }
      for (IDSClass childClass : instance.getClasses()) {
         iterateOverClass(childClass);
      }
      for (IDSInterface childInterface : instance.getInterfaces()) {
         iterateOverInterface(childInterface);
      }
      for (IDSEnum childEnums : instance.getEnums()) {
         iterateOverEnum(childEnums);
      }
   }

   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnPackage(IDSPackage instance) throws DSException {
   }

   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverType(IDSType instance) throws DSException {
      iterateOverProvable(instance);
      for (IDSClass childClass : instance.getInnerClasses()) {
         iterateOverClass(childClass);
      }
      for (IDSInterface childInterface : instance.getInnerInterfaces()) {
         iterateOverInterface(childInterface);
      }
      for (IDSEnum childEnums : instance.getInnerEnums()) {
         iterateOverEnum(childEnums);
      }
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverProvable(IDSProvable instance) throws DSException {
      for (String obligation : instance.getObligations()) {
         iterateOverObligation(obligation);
      }
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverClass(IDSClass instance) throws DSException {
      workOnClass(instance);
      iterateOverType(instance);
      for (IDSMethod method : instance.getMethods()) {
         iterateOverMethod(method);
      }
      for (IDSConstructor constructor : instance.getConstructors()) {
         iterateOverConstructor(constructor);
      }
      for (IDSAttribute attribute : instance.getAttributes()) {
         iterateOverAttribute(attribute);
      }
      for (IDSInvariant invariant : instance.getInvariants()) {
         iterateOverInvariant(invariant);
      }
      for (IDSAxiom axiom : instance.getAxioms()) {
         iterateOverAxiom(axiom);
      }
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnClass(IDSClass instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverInterface(IDSInterface instance) throws DSException {
      workOnInterface(instance);
      iterateOverType(instance);
      for (IDSMethod method : instance.getMethods()) {
         iterateOverMethod(method);
      }
      for (IDSAttribute attribute : instance.getAttributes()) {
         iterateOverAttribute(attribute);
      }
      for (IDSInvariant invariant : instance.getInvariants()) {
         iterateOverInvariant(invariant);
      }
      for (IDSAxiom axiom : instance.getAxioms()) {
         iterateOverAxiom(axiom);
      }
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnInterface(IDSInterface instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverEnum(IDSEnum instance) throws DSException {
      workOnEnum(instance);
      iterateOverType(instance);
      for (IDSMethod method : instance.getMethods()) {
         iterateOverMethod(method);
      }
      for (IDSConstructor constructor : instance.getConstructors()) {
         iterateOverConstructor(constructor);
      }      
      for (IDSAttribute attribute : instance.getAttributes()) {
         iterateOverAttribute(attribute);
      }
      for (IDSInvariant invariant : instance.getInvariants()) {
         iterateOverInvariant(invariant);
      }
      for (IDSAxiom axiom : instance.getAxioms()) {
         iterateOverAxiom(axiom);
      }
      for (IDSEnumLiteral literal : instance.getLiterals()) {
         iterateOverEnumLiteral(literal);
      }      
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnEnum(IDSEnum instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverMethod(IDSMethod instance) throws DSException {
      workOnMethod(instance);
      iterateOverOperation(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnMethod(IDSMethod instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverConstructor(IDSConstructor instance) throws DSException {
      iterateOverProvable(instance);
      workOnConstructor(instance);
      iterateOverOperation(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnConstructor(IDSConstructor instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverOperation(IDSOperation instance) throws DSException {
      iterateOverProvable(instance);
      for (IDSOperationContract operationContract : instance.getOperationContracts()) {
         iterateOverOperationContract(operationContract);
      }
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverOperationContract(IDSOperationContract instance) throws DSException {
      workOnOperationContract(instance);
      iterateOverProvable(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnOperationContract(IDSOperationContract instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverAttribute(IDSAttribute instance) throws DSException {
      workOnAttribute(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnAttribute(IDSAttribute instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverInvariant(IDSInvariant instance) throws DSException {
      workOnInvariant(instance);
      iterateOverProvable(instance);
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverAxiom(IDSAxiom instance) throws DSException {
      workOnAxiom(instance);
      for (IDSAxiomContract axiomContract : instance.getAxiomContracts()) {
         iterateOverAxiomContract(axiomContract);
      }
      iterateOverProvable(instance);
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverAxiomContract(IDSAxiomContract instance) throws DSException {
      workOnAxiomContract(instance);
      iterateOverProvable(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnInvariant(IDSInvariant instance) throws DSException {
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnAxiom(IDSAxiom instance) throws DSException {
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnAxiomContract(IDSAxiomContract instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverObligation(String instance) throws DSException {
      workOnObligation(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnObligation(String instance) throws DSException {
   }
   
   /**
    * Iterates over the current element.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   public void iterateOverEnumLiteral(IDSEnumLiteral instance) throws DSException {
      workOnEnumLiteral(instance);
   }
   
   /**
    * Subclasses can do something with the current element.
    * This default implementation does nothing.
    * @param instance The current element.
    * @throws DSException Occurred Exception.
    */
   protected void workOnEnumLiteral(IDSEnumLiteral instance) throws DSException {
   }
}