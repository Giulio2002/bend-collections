"""Regression tests for targeted validation without requiring the Bend compiler."""

import importlib.util
import json
import os
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest.mock import Mock, patch


class TargetedValidationTest(unittest.TestCase):
    def test_only_backend_diff_succeeds_without_running_lru(self):
        source = Path(__file__).with_name('validate.py')
        with patch.dict(os.environ, {'BEND': sys.executable}):
            spec = importlib.util.spec_from_file_location('bend_validate_for_test', source)
            validator = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(validator)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('src', 'tests', 'tools', 'build/backend_diff'):
                (root / name).mkdir(parents=True)
            (root / 'tests/structures.json').write_text(
                json.dumps({'new_structures': [{'id': 'dynamic_array'}]})
            )
            (root / 'build/backend_diff/report.json').write_text(json.dumps({'passed': True}))
            report_path = root / 'report.json'
            lru = Mock(return_value=(True, {'checks': []}))
            validator.FAILURES.clear()
            with patch.object(validator, 'ROOT', root), \
                    patch.object(validator, 'LOGDIR', root / 'build/validation-logs'), \
                    patch.object(validator, 'run', return_value=types.SimpleNamespace(
                        returncode=0, stdout='', stderr='')), \
                    patch.object(validator, 'check_lru', lru), \
                    patch.object(sys, 'argv', ['validate.py', '--report', str(report_path),
                                               '--only', 'backend_diff']):
                exit_code = validator.main()

            report = json.loads(report_path.read_text())
            self.assertEqual(report['backend_diff']['differential'], 'passed')
            self.assertEqual(report['failures'], [])
            self.assertEqual(exit_code, 0)
            self.assertFalse(report['complete'])
            self.assertEqual(report['lru_reuse'], 'not_run')
            lru.assert_not_called()

    def test_unknown_target_is_rejected(self):
        source = Path(__file__).with_name('validate.py')
        with patch.dict(os.environ, {'BEND': sys.executable}):
            spec = importlib.util.spec_from_file_location('bend_validate_for_test', source)
            validator = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(validator)

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'tests').mkdir()
            (root / 'tests/structures.json').write_text(json.dumps({'new_structures': []}))
            with patch.object(validator, 'ROOT', root), \
                    patch.object(sys, 'argv', ['validate.py', '--report', str(root / 'report.json'),
                                               '--only', 'missing']):
                with self.assertRaises(SystemExit) as error:
                    validator.main()
            self.assertEqual(error.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
