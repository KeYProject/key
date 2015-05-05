package org.key_project.sed.key.evaluation.model;

import java.util.List;

import org.key_project.util.java.CollectionUtil;

public class Form {
   private final String name;
   
   private final List<AbstractPage> pages;

   public Form(String name, AbstractPage... pages) {
      this(name, CollectionUtil.toList(pages));
   }

   public Form(String name, List<AbstractPage> pages) {
      this.name = name;
      this.pages = pages;
   }

   public String getName() {
      return name;
   }

   public AbstractPage[] getPages() {
      return pages.toArray(new AbstractPage[pages.size()]);
   }

   public int countPages() {
      return pages.size();
   }
}
