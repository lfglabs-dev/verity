#!/usr/bin/env python3
"""Tests for check_dead_private_decls.py."""
from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_dead_private_decls as dead


def _src(text: str) -> str:
    return textwrap.dedent(text).lstrip("\n")


def _dead_names(text: str) -> list[str]:
    _, _, blocks = dead.find_dead(_src(text))
    return [n for b in blocks for n in b.names]


class FindDeadTests(unittest.TestCase):
    def test_unused_private_is_dead(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                private theorem helper : True := trivial

                theorem pub : True := trivial
                """
            ),
            ["helper"],
        )

    def test_private_used_by_public_is_live(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                private theorem helper : True := trivial

                theorem pub : True := helper
                """
            ),
            [],
        )

    def test_transitive_reachability(self) -> None:
        names = _dead_names(
            """
            private def a : Nat := 1
            private def b : Nat := a
            private def c : Nat := 2
            private def d : Nat := c

            def pub : Nat := b
            """
        )
        self.assertEqual(sorted(names), ["c", "d"])

    def test_private_cycle_without_root_is_dead(self) -> None:
        names = _dead_names(
            """
            private theorem a : True := b
            private theorem b : True := a
            """
        )
        self.assertEqual(sorted(names), ["a", "b"])

    def test_simp_attribute_pins_private(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                @[simp] private theorem helper : True := trivial
                """
            ),
            [],
        )

    def test_harmless_attribute_does_not_pin(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                @[reducible] private def helper : Nat := 1
                """
            ),
            ["helper"],
        )

    def test_comment_mention_is_not_a_use(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                private theorem helper : True := trivial

                /-- Mentions `helper` only in prose. -/
                theorem pub : True := trivial -- helper
                """
            ),
            ["helper"],
        )

    def test_dot_notation_and_generated_names_count_as_use(self) -> None:
        names = _dead_names(
            """
            private theorem Foo.helper : True := trivial
            private def f : Nat → Nat
              | 0 => 0
              | n + 1 => f n

            theorem pub (x : Foo) : True := x.helper
            theorem pub2 : f 0 = 0 := by simp [f.eq_1]
            """
        )
        self.assertEqual(names, [])

    def test_use_after_unicode_bracket_or_arrow(self) -> None:
        names = _dead_names(
            """
            private theorem a : True := trivial
            private theorem b : True := trivial
            private theorem c₁ : True := trivial

            theorem pub : True ∧ True := ⟨a, by rw [←b]; exact c₁⟩
            """
        )
        self.assertEqual(names, [])

    def test_attribute_command_counts_as_use(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                private theorem helper : True := trivial

                attribute [local simp] helper
                """
            ),
            [],
        )

    def test_split_header_name(self) -> None:
        self.assertEqual(
            _dead_names(
                """
                private theorem
                    veryLongHelperName : True := trivial
                """
            ),
            ["veryLongHelperName"],
        )

    def test_mutual_block_is_one_unit(self) -> None:
        text = """
            mutual
            private def even : Nat → Bool
              | 0 => true
              | n + 1 => odd n
            private def odd : Nat → Bool
              | 0 => false
              | n + 1 => even n
            end
            """
        self.assertEqual(sorted(_dead_names(text)), ["even", "odd"])
        self.assertEqual(_dead_names(text + "\ndef pub := odd 3\n"), [])

    def test_mutual_with_public_member_is_kept(self) -> None:
        names = _dead_names(
            """
            mutual
            private def even : Nat → Bool
              | 0 => true
              | n + 1 => odd n
            def odd : Nat → Bool
              | 0 => false
              | n + 1 => even n
            end
            """
        )
        self.assertEqual(names, [])

    def test_public_and_protected_are_never_reported(self) -> None:
        names = _dead_names(
            """
            theorem pub : True := trivial
            protected def prot : Nat := 0
            private instance : Inhabited Nat := ⟨0⟩
            """
        )
        self.assertEqual(names, [])


class PruneTests(unittest.TestCase):
    def test_prune_removes_doc_comment_and_attrs(self) -> None:
        text = _src(
            """
            namespace X

            /-- Dead helper.

            Its doc comment has a blank line. -/
            @[reducible]
            private def helper : Nat := 1

            /-- Live. -/
            def pub : Nat := 2

            end X
            """
        )
        out, removed = dead.prune(text)
        self.assertEqual(removed, ["helper"])
        self.assertEqual(
            out,
            _src(
                """
                namespace X

                /-- Live. -/
                def pub : Nat := 2

                end X
                """
            ),
        )

    def test_prune_keeps_section_header_after_dead_block(self) -> None:
        text = _src(
            """
            private theorem helper : True := by
              trivial

            /-! ## Section -/

            theorem pub : True := trivial
            """
        )
        out, _ = dead.prune(text)
        self.assertEqual(
            out,
            _src(
                """
                /-! ## Section -/

                theorem pub : True := trivial
                """
            ),
        )

    def test_prune_keeps_module_doc_directly_above(self) -> None:
        text = _src(
            """
            theorem pub : True := trivial

            /-! ## Section -/
            private theorem helper : True := trivial
            """
        )
        out, _ = dead.prune(text)
        self.assertIn("/-! ## Section -/", out)
        self.assertNotIn("helper", out)

    def test_prune_removes_set_option_prefix_and_where_clause(self) -> None:
        text = _src(
            """
            set_option maxHeartbeats 400000 in
            private def helper : Nat := go 3
            where
              go : Nat → Nat
                | 0 => 0
                | n + 1 => go n
            termination_by n => n

            def pub : Nat := 0
            """
        )
        out, removed = dead.prune(text)
        self.assertEqual(removed, ["helper"])
        self.assertEqual(out, "def pub : Nat := 0\n")

    def test_prune_reaches_fixpoint_in_one_pass(self) -> None:
        text = _src(
            """
            private def a : Nat := 1
            private def b : Nat := a

            def pub : Nat := 0
            """
        )
        once, _ = dead.prune(text)
        twice, removed = dead.prune(once)
        self.assertEqual(once, twice)
        self.assertEqual(removed, [])


class MainTests(unittest.TestCase):
    def _run(self, *args: str) -> tuple[int, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = dead.main(list(args))
        return code, out.getvalue() + err.getvalue()

    def test_check_and_fix(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "A.lean"
            path.write_text(
                "private theorem helper : True := trivial\n\ntheorem pub : True := trivial\n",
                encoding="utf-8",
            )
            code, out = self._run("--check", str(path))
            self.assertEqual(code, 1)
            self.assertIn("dead private declaration `helper`", out)

            code, out = self._run("--fix", str(path))
            self.assertEqual(code, 0)
            self.assertEqual(path.read_text(encoding="utf-8"), "theorem pub : True := trivial\n")

            code, out = self._run("--check", str(path))
            self.assertEqual(code, 0)
            self.assertIn("passed", out)


if __name__ == "__main__":
    unittest.main()
