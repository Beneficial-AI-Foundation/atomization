import re
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple, Self
import json
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.structs import TermType


class Atom(NamedTuple):
    termtype: str
    identifier: str
    lineno: int
    spec: str
    deps: list[Self]
    proof: list[str]

    def __str__(self) -> str:
        return f"{self.identifier} : {self.spec} := {self.proof}"


type Atoms = list[Atom]


@dataclass
class Atomizer:
    filename: Path


class CoqAtomizer(Atomizer):
    def atomize(self) -> Atoms:
        pattern_thm_lma = r"(Theorem|Lemma)\s+(\w+)\s*:\s*(.*)"
        pattern_inductive = r"(Inductive|Variant|CoInductive)\s+(\w+)\s*:\s*((?:\w+(?:\s+\w+)*?))\s*:=\s*((?:.|[\r\n])*)"
        pattern_notation = r"(Notation|Infix)\s+(?:\"([^\"]*)\"|([^\s:=]+))\s*:=\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\)(?:\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\))?(?:\s*:\s*([a-zA-Z_][a-zA-Z0-9_]*_scope))?\s*\."
        with ProofFile(str(self.filename)) as pf:
            pf.run()
            result = []
            for proof in pf.proofs:
                context = []
                for item in proof.context:
                    match item.type:
                        case TermType.THEOREM | TermType.LEMMA:
                            term_type, name, signature = re.match(
                                pattern_thm_lma, item.step.short_text
                            ).groups()
                            atom = Atom(
                                term_type,
                                name,
                                item.step.ast.range.start.line,
                                signature,
                                [],
                                [],
                            )
                            context.append(atom)
                        case (
                            TermType.DEFINITION
                            | TermType.FIXPOINT
                            | TermType.COFIXPOINT
                            | TermType.FUNCTION
                        ):
                            continue
                        case (
                            TermType.INDUCTIVE | TermType.VARIANT | TermType.COINDUCTIVE
                        ):
                            term_type, name, _, defn = re.match(
                                pattern_inductive, item.step.short_text
                            ).groups()
                            atom = Atom(
                                term_type,
                                name,
                                item.step.ast.range.start.line,
                                defn,
                                [],
                                [],
                            )
                            context.append(atom)
                        # case TermType.NOTATION:
                        #    groups = re.match(
                        #        pattern_notation, item.step.short_text
                        #    ).groups()
                        #    notation = next(g for g in groups[:2] if g is not None)
                        #    # Shift remaining groups based on which notation matched
                        #    definition = groups[2]
                        #    options = groups[3] if groups[3] else None
                        #    scope = groups[4]
                        #    atom = Atom(
                        #        "Notation",
                        #        notation,
                        #        item.step.ast.range.start.line,
                        #        definition,
                        #        [],
                        #        [],
                        #    )
                        #    context.append(atom)
                        case _:
                            """
                            TermType.RECORD
                            TermType.CLASS
                            TermType.INSTANCE
                            TermType.SCHEME
                            TermType.FACT
                            TermType.REMARK
                            TermType.COROLLARY
                            TermType.PROPOSITION
                            TermType.PROPERTY
                            TermType.OBLIGATION
                            TermType.TACTIC
                            TermType.RELATION
                            TermType.SETOID
                            TermType.DERIVE
                            TermType.EQUATION
                            TermType.OTHER
                            """
                            continue

                term_type, name, signature = re.match(
                    pattern_thm_lma, proof.step.short_text
                ).groups()
                atom = Atom(
                    term_type,
                    name,
                    proof.step.ast.range.start.line,
                    signature,
                    context,
                    [str(x) for x in proof.steps],
                )
                result.append(atom)
        return result

    def jsonify(self) -> str:
        atoms = self.atomize()
        return json.dumps([atom._asdict() for atom in atoms])


def main() -> None:
    examples = Path("examples")
    atomizer = CoqAtomizer(examples / "minimal.v")
    print(atomizer.jsonify())
