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

package de.hentschel.visualdbc.statistic.ui.emfAdapter;

import java.util.List;

import org.eclipse.emf.common.notify.Adapter;
import org.eclipse.emf.common.notify.Notifier;
import org.eclipse.emf.edit.provider.ITableItemLabelProvider;

import de.hentschel.visualdbc.dbcmodel.DbcClass;
import de.hentschel.visualdbc.dbcmodel.DbcConstructor;
import de.hentschel.visualdbc.dbcmodel.DbcEnum;
import de.hentschel.visualdbc.dbcmodel.DbcInterface;
import de.hentschel.visualdbc.dbcmodel.DbcMethod;
import de.hentschel.visualdbc.dbcmodel.DbcOperationContract;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.provider.DbCAxiomContractItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcAxiomItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcClassItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcConstructorItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcEnumItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcInterfaceItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcMethodItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcModelItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcOperationContractItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcPackageItemProvider;
import de.hentschel.visualdbc.dbcmodel.provider.DbcmodelItemProviderAdapterFactory;

/**
 * Special {@link DbcmodelItemProviderAdapterFactory} in that children are filtered
 * for statistic purpose. That means that only provable children are returned.
 * @author Martin Hentschel
 */
public class StatisticDbcmodelItemProviderAdapterFactory extends DbcmodelItemProviderAdapterFactory {
   /**
    * The sued {@link StatisticDbcModelItemProvider} instead of the {@link DbcModelItemProvider}.
    */
   private StatisticDbcModelItemProvider statisticDbcModelItemProvider;

   /**
    * The sued {@link StatisticDbcPackageItemProvider} instead of the {@link DbcPackageItemProvider}.
    */
   private StatisticDbcPackageItemProvider statisticDbcPackageItemProvider;

   /**
    * The sued {@link StatisticDbcInterfaceItemProvider} instead of the {@link DbcInterfaceItemProvider}.
    */
   private StatisticDbcInterfaceItemProvider statisticDbcInterfaceItemProvider;

   /**
    * The sued {@link StatisticDbcClassItemProvider} instead of the {@link DbcClassItemProvider}.
    */
   private StatisticDbcClassItemProvider statisticDbcClassItemProvider;

   /**
    * The sued {@link StatisticDbcEnumItemProvider} instead of the {@link DbcEnumItemProvider}.
    */
   private StatisticDbcEnumItemProvider statisticDbcEnumItemProvider;

   /**
    * The sued {@link StatisticDbcMethodItemProvider} instead of the {@link DbcMethodItemProvider}.
    */
   private StatisticDbcMethodItemProvider statisticDbcMethodItemProvider;

   /**
    * The sued {@link StatisticDbcConstructorItemProvider} instead of the {@link DbcConstructorItemProvider}.
    */
   private StatisticDbcConstructorItemProvider statisticDbcConstructorItemProvider;

   /**
    * The sued {@link StatisticDbcOperationContractItemProvider} instead of the {@link DbcOperationContractItemProvider}.
    */
   private StatisticDbcOperationContractItemProvider statisticDbcOperationContractItemProvider;

   /**
    * The sued {@link StatisticDbcAxiomItemProvider} instead of the {@link DbcAxiomItemProvider}.
    */
   private StatisticDbcAxiomItemProvider statisticDbcAxiomItemProvider;

   /**
    * The sued {@link StatisticDbcAxiomContractItemProvider} instead of the {@link DbCAxiomContractItemProvider}.
    */
   private StatisticDbcAxiomContractItemProvider statisticDbcAxiomContractItemProvider;
   
   /**
    * The shown {@link DbCProofObligation}s in the columns after the main column.
    * The order in that list defines what is shown in the cells.
    */
   private List<DbcProofObligation> columnProofObligations;
   
   /**
    * Constructor.
    * @param columnProofObligations The shown {@link DbCProofObligation}s in the columns after the main column.
    */
   public StatisticDbcmodelItemProviderAdapterFactory(List<DbcProofObligation> columnProofObligations) {
      this.columnProofObligations = columnProofObligations;
      // Support columns in label providers
      supportedTypes.add(ITableItemLabelProvider.class);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcModelAdapter() {
      if (statisticDbcModelItemProvider == null) {
         statisticDbcModelItemProvider = new StatisticDbcModelItemProvider(this);
      }
      return statisticDbcModelItemProvider;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcPackageAdapter() {
      if (statisticDbcPackageItemProvider == null) {
         statisticDbcPackageItemProvider = new StatisticDbcPackageItemProvider(this);
      }
      return statisticDbcPackageItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcInterfaceAdapter() {
      if (statisticDbcInterfaceItemProvider == null) {
         statisticDbcInterfaceItemProvider = new StatisticDbcInterfaceItemProvider(this);
      }
      return statisticDbcInterfaceItemProvider;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcClassAdapter() {
      if (statisticDbcClassItemProvider == null) {
         statisticDbcClassItemProvider = new StatisticDbcClassItemProvider(this);
      }
      return statisticDbcClassItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcEnumAdapter() {
      if (statisticDbcEnumItemProvider == null) {
         statisticDbcEnumItemProvider = new StatisticDbcEnumItemProvider(this);
      }
      return statisticDbcEnumItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcAxiomAdapter() {
      if (statisticDbcAxiomItemProvider == null) {
         statisticDbcAxiomItemProvider = new StatisticDbcAxiomItemProvider(this);
      }
      return statisticDbcAxiomItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbCAxiomContractAdapter() {
      if (statisticDbcAxiomContractItemProvider == null) {
         statisticDbcAxiomContractItemProvider = new StatisticDbcAxiomContractItemProvider(this);
      }
      return statisticDbcAxiomContractItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcMethodAdapter() {
      if (statisticDbcMethodItemProvider == null) {
         statisticDbcMethodItemProvider = new StatisticDbcMethodItemProvider(this);
      }
      return statisticDbcMethodItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcConstructorAdapter() {
      if (statisticDbcConstructorItemProvider == null) {
         statisticDbcConstructorItemProvider = new StatisticDbcConstructorItemProvider(this);
      }
      return statisticDbcConstructorItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Adapter createDbcOperationContractAdapter() {
      if (statisticDbcOperationContractItemProvider == null) {
         statisticDbcOperationContractItemProvider = new StatisticDbcOperationContractItemProvider(this);
      }
      return statisticDbcOperationContractItemProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (statisticDbcClassItemProvider != null) {
         statisticDbcClassItemProvider.dispose();
      }
      if (statisticDbcConstructorItemProvider != null) {
         statisticDbcConstructorItemProvider.dispose();
      }
      if (statisticDbcEnumItemProvider != null) {
         statisticDbcEnumItemProvider.dispose();
      }
      if (statisticDbcInterfaceItemProvider != null) {
         statisticDbcInterfaceItemProvider.dispose();
      }
      if (statisticDbcMethodItemProvider != null) {
         statisticDbcMethodItemProvider.dispose();
      }
      if (statisticDbcModelItemProvider != null) {
         statisticDbcModelItemProvider.dispose();
      }
      if (statisticDbcOperationContractItemProvider != null) {
         statisticDbcOperationContractItemProvider.dispose();
      }
      if (statisticDbcPackageItemProvider != null) {
         statisticDbcPackageItemProvider.dispose();
      }
      if (statisticDbcAxiomItemProvider != null) {
         statisticDbcAxiomItemProvider.dispose();
      }
      if (statisticDbcAxiomContractItemProvider != null) {
         statisticDbcAxiomContractItemProvider.dispose();
      }
      super.dispose();
   }

   /**
    * Returns the shown {@link DbCProofObligation}s in the columns.
    * @return The shown {@link DbCProofObligation} in the columns.
    */
   public List<DbcProofObligation> getColumnProofObligations() {
      return columnProofObligations;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void associate(Adapter adapter, Notifier target) {
      // Also observe the available proofs in the child adapters (Listener are automatically removed at dispose())
      if (target instanceof DbcClass) {
         for (DbcProof proof : ((DbcClass)target).getAllProofs()) {
            if (!proof.eAdapters().contains(createDbcClassAdapter())) {
               proof.eAdapters().add(createDbcClassAdapter());
            }
         }
      }
      else if (target instanceof DbcInterface) {
         for (DbcProof proof : ((DbcInterface)target).getAllProofs()) {
            if (!proof.eAdapters().contains(createDbcInterfaceAdapter())) {
               proof.eAdapters().add(createDbcInterfaceAdapter());
            }
         }
      }
      else if (target instanceof DbcEnum) {
         for (DbcProof proof : ((DbcEnum)target).getAllProofs()) {
            if (!proof.eAdapters().contains(createDbcEnumAdapter())) {
               proof.eAdapters().add(createDbcEnumAdapter());
            }
         }
      }
      else if (target instanceof DbcConstructor) {
         for (DbcProof proof : ((DbcConstructor)target).getAllProofs()) {
            if (!proof.eAdapters().contains(createDbcConstructorAdapter())) {
               proof.eAdapters().add(createDbcConstructorAdapter());
            }
         }
      }
      else if (target instanceof DbcMethod) {
         for (DbcProof proof : ((DbcMethod)target).getAllProofs()) {
            if (!proof.eAdapters().contains(createDbcMethodAdapter())) {
               proof.eAdapters().add(createDbcMethodAdapter());
            }
         }
      }
      else if (target instanceof DbcOperationContract) {
         for (DbcProof proof : ((DbcOperationContract)target).getAllProofs()) {
            if (!proof.eAdapters().contains(createDbcOperationContractAdapter())) {
               proof.eAdapters().add(createDbcOperationContractAdapter());
            }
         }
      }
      // Observe target
      super.associate(adapter, target);
   }
}