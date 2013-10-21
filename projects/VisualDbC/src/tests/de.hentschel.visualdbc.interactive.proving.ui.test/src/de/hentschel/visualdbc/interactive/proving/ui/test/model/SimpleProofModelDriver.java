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

package de.hentschel.visualdbc.interactive.proving.ui.test.model;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSDriver;
import de.hentschel.visualdbc.datasource.model.memory.MemoryAttribute;
import de.hentschel.visualdbc.datasource.model.memory.MemoryClass;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnection;

/**
 * An {@link IDSDriver} that allows interactive proofs for test purpose.
 * @author Martin Hentschel
 */
public class SimpleProofModelDriver extends AbstractDSDriver {
   /**
    * The ID of this driver.
    */
   public static final String ID = "de.hentschel.visualdbc.dbcmodel.diagram.custom.test.simpleProofModel";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public int getPriority() {
      return Integer.MIN_VALUE;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Simple Proof Model";
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSConnectionSetting> getConnectionSettings() {
      return new LinkedList<IDSConnectionSetting>();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSConnection createConnection() throws DSException {
      // Create connection
      MemoryConnection connection = new MemoryConnection(this);
      MemoryClass mCDemo = new MemoryClass("MCDemo");
      connection.addClass(mCDemo);
      MemoryAttribute attr = new MemoryAttribute("attr", "int", DSVisibility.PRIVATE);
      mCDemo.getAttributes().add(attr);
      LoggingMethod inc = new LoggingMethod("inc(x : int)", "int", DSVisibility.PUBLIC);
      inc.getObligations().add("PreservesInv");
      mCDemo.addMethod(inc);
      LoggingOperationContract c0 = new LoggingOperationContract("JML normal_behavior operation contract (id: 0)", "true", "exc = null", "{}", "diamond");
      c0.getObligations().add("EnsuresPost");
      inc.addOperationContract(c0);
      LoggingMethod init = new LoggingMethod("init(u : int)", "int", DSVisibility.PUBLIC);
      mCDemo.addMethod(init);
      LoggingOperationContract c1 = new LoggingOperationContract("JML normal_behavior operation contract (id: 1)", "true", "result = (jint)(javaAddInt(u, (jint)(1)))\n& self.attr = (jint)(100)\n& exc = null", "{}", "diamond");
      c1.getObligations().add("EnsuresPost");
      c1.getObligations().add("RespectsModifies");
      init.addOperationContract(c1);
      return connection;
   }
}