import re
from dataclasses import dataclass
from pathlib import Path
from typing import NamedTuple
from coqpyt.coq.structs import TermType
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.exceptions import InvalidChangeException


class Atom(NamedTuple):
    identifier: str
    spec: str
    proof: list[str]

    def __str__(self) -> str:
        return f"{self.identifier} : {self.spec} := {self.proof}"


type Atoms = list[Atom]


@dataclass
class Atomizer:
    filename: Path


class CoqAtomizer(Atomizer):
    def atomize(self) -> Atoms:
        pattern = r"(Theorem|Lemma)\s+(\w+)\s*:\s*(.*)"
        with ProofFile(str(self.filename)) as pf:
            pf.run()
            result = []
            for proof in pf.proofs:
                _, name, signature = re.match(pattern, proof.step.short_text).groups()

                atom = Atom(name, signature, [str(x) for x in proof.steps])
                result.append(atom)
        return result


def main() -> None:
    examples = Path("examples")
    atomizer = CoqAtomizer(examples / "minimal.v")
    for atom in atomizer.atomize():
        print(atom)
