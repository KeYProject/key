/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir;

import org.key_project.rusty.parser.hir.expr.BlockCheckMode;
import org.key_project.rusty.parser.hir.expr.ExprKind;
import org.key_project.rusty.parser.hir.expr.LitIntTy;
import org.key_project.rusty.parser.hir.expr.LitKind;
import org.key_project.rusty.parser.hir.hirty.HirTyKind;
import org.key_project.rusty.parser.hir.hirty.PrimHirTy;
import org.key_project.rusty.parser.hir.item.FnRetTy;
import org.key_project.rusty.parser.hir.item.ItemKind;
import org.key_project.rusty.parser.hir.pat.ByRef;
import org.key_project.rusty.parser.hir.pat.PatKind;
import org.key_project.rusty.parser.hir.stmt.LocalSource;
import org.key_project.rusty.parser.hir.stmt.StmtKind;
import org.key_project.rusty.parser.hir.ty.Ty;

import com.google.gson.FieldNamingPolicy;
import com.google.gson.GsonBuilder;

public record Crate(Mod topMod,HirTyMapping[]types){public record WrapperOutput(Crate crate,Specs specs){}

public static WrapperOutput parseJSON(String json){var gson=new GsonBuilder().setFieldNamingPolicy(FieldNamingPolicy.LOWER_CASE_WITH_UNDERSCORES).registerTypeAdapter(ItemKind.class,new ItemKind.Adapter()).registerTypeAdapter(FnRetTy.class,new FnRetTy.Adapter()).registerTypeAdapter(HirTyKind.class,new HirTyKind.Adapter()).registerTypeAdapter(PrimHirTy.class,new PrimHirTy.Adapter()).registerTypeAdapter(QPath.class,new QPath.Adapter()).registerTypeAdapter(Res.class,new Res.Adapter()).registerTypeAdapter(PatKind.class,new PatKind.Adapter()).registerTypeAdapter(LitKind.class,new LitKind.Adapter()).registerTypeAdapter(LitIntTy.class,new LitIntTy.Adapter()).registerTypeAdapter(BlockCheckMode.class,new BlockCheckMode.Adapter()).registerTypeAdapter(LocalSource.class,new LocalSource.Adapter()).registerTypeAdapter(ExprKind.class,new ExprKind.Adapter()).registerTypeAdapter(ByRef.class,new ByRef.Adapter()).registerTypeAdapter(StmtKind.class,new StmtKind.Adapter()).registerTypeAdapter(DefKind.class,new DefKind.Adapter()).registerTypeAdapter(Ty.class,new Ty.Adapter()).create();return gson.fromJson(json,WrapperOutput.class);}}
