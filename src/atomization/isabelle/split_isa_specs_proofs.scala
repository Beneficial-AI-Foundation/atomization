package isabelle

object Test_Thy_Parser {
  
  private def is_definition(span: Command_Span.Span, keywords: Keyword.Keywords): Boolean = {
    if (span.toString().contains("malformed")) {
        println(s"Warning: Malformed span detected : ${span}")
      }
    keywords.kinds.get(span.name) match {
      case Some(kind) => Keyword.theory_defn.contains(kind)
      case None => false
    }
  }

  private def is_proof(span: Command_Span.Span, keywords: Keyword.Keywords): Boolean = {
    if (span.toString().contains("malformed")) {
        println(s"Warning: Malformed span detected: ${span}")
      }
    keywords.kinds.get(span.name) match {
      case Some(kind) => Keyword.proof.contains(kind)
      case None => false
    }
  }

  private def write_spans(path: Path, spans: List[Command_Span.Span]): Unit = {
    val content = new StringBuilder()
    spans.zipWithIndex.foreach { case (span, index) =>
      content.append(span.content.map(_.source).mkString(" "))
      spans.lift(index + 1).foreach { nextSpan =>
        if (!Set("(", ")", "[code]", "by", "proof").contains(nextSpan.name)) {
          content.append("\n\n")
        } else if (nextSpan.name == "[code]") {
          content.append(" ")
        } else if (nextSpan.name == "by") {
          content.append("\n ")
        } else if (nextSpan.name == "proof") {
          content.append("\n")
        }
      }
    }
    File.write(path, content.toString)
  }

  private def create_root_file(theory_name: String, directory: Path): Unit = {
    val root_content = s"""session Test = HOL +
      theories
      $theory_name"""
    val root_path = directory + Path.explode("ROOT")
    File.write(root_path, root_content)
  }

  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      println("Usage: isabelle scala -e 'split_isa_spec_proofs.scala' <theory_file.thy>")
      sys.exit(1)
    }

    val thy_file = Path.explode(args(0))
    if (!thy_file.is_file) {
      println(s"Error: File not found - ${thy_file}")
      sys.exit(1)
    }

    type Keywords = List[(String, Keyword.Spec)]

    val thy_keywords : Keywords = List(("%", Keyword.Spec()),
      ("(", Keyword.Spec()),
      (")", Keyword.Spec()), 
      (",", Keyword.Spec()), 
      ("::", Keyword.Spec()),
      (":", Keyword.Spec()),
      ("..", Keyword.Spec()),    
      ("=", Keyword.Spec()), 
      ("and", Keyword.Spec()),
      ("[code]", Keyword.Spec()),
      ("export_code", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("export_code"))),
      //("begin", Keyword.Spec(kind = Keyword.QUASI_COMMAND)),
      ("text", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("fun", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("fun"))),
      ("function", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("function"))),
      ("datatype", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("datatype"))),
      ("definition", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("definition"))),
      ("theory", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("theory"))),
      ("proof", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("proof"))),
      ("lemma", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("lemma"))),
      ("qed", Keyword.Spec(kind = Keyword.QED, tags = List("qed"))),
      ("by", Keyword.Spec(kind = Keyword.PRF_ASM_GOAL, tags = List("by"))),
      ("next", Keyword.Spec(kind = Keyword.NEXT_BLOCK, tags = List("next"))),
      ("end", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("end")))
      )

    // Setup syntax with common theory keywords
    val thy_syntax = Outer_Syntax.empty.add_keywords(thy_keywords)
      
    // Read and parse theory content
    val theory_content = File.read(thy_file)
    val spans = thy_syntax.parse_spans(theory_content)


    // Separate definitions and proofs
    val (definitions, proofs) = spans.partition(span => is_definition(span, thy_syntax.keywords))
    val generates_code = spans.exists(_.name == "export_code")

    // Generate output files
    val base_path = thy_file.expand.implode
    val def_path = Path.explode(base_path.replaceAll("\\.thy$", "_definitions.thy"))
    val proof_path = Path.explode(base_path.replaceAll("\\.thy$", "_proofs.thy"))

    write_spans(def_path, definitions)
    write_spans(proof_path, proofs)

    if (generates_code) {
      val theory_name = thy_file.base.implode.replaceAll("\\.thy$", "")
      create_root_file(theory_name, thy_file.dir)
      val export_command = s"isabelle export -d . -x *:** Test"
      val process = Runtime.getRuntime.exec(export_command)
      process.waitFor()
      println(s"Executed command: $export_command")
    }

    // Report results
    println(s"\nProcessed theory file: ${thy_file}")
    println("Generated files:")
    println(s"  Definitions: ${def_path}")
    println(s"  Proofs: ${proof_path}")
    println(s"\nFound ${definitions.length} definitions and ${proofs.length} proofs")
  }
}
