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
    /*
    println(span)
    println(span.name)
    println("--end name--")
    println(keywords.kinds.get(span.name))
    println("--end kind--")
    println(Keyword.proof)
    println("--end Keyword.proof--")
    */
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
    val definitions = spans.filter(span => is_definition(span, thy_syntax.keywords))
    val proofs = spans.filter(span => is_proof(span, thy_syntax.keywords))

    // Generate output files
    val base_path = thy_file.expand.implode
    val def_path = Path.explode(base_path.replaceAll("\\.thy$", "_definitions.thy"))
    val proof_path = Path.explode(base_path.replaceAll("\\.thy$", "_proofs.thy"))

    write_spans(def_path, definitions)
    write_spans(proof_path, proofs)

    // Report results
    println(s"\nProcessed theory file: ${thy_file}")
    println("Generated files:")
    println(s"  Definitions: ${def_path}")
    println(s"  Proofs: ${proof_path}")
    println(s"\nFound ${definitions.length} definitions and ${proofs.length} proofs")
  }
}
