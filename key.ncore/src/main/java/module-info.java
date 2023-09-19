module org.key_project.ncore {
   requires org.key_project.util;
   requires jsr305;

   /* requires, exports, uses */
   exports org.key_project.logic;
   exports org.key_project.logic.op;
   exports org.key_project.logic.sort;
   exports org.key_project.rule;
}