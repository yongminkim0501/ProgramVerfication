import sys

def get_file(file_path):
  with open(file_path, 'r') as f:
    lines = f.readlines()
    check = False
    clauses_dict = {}
    clauses_count = 1
    for line in lines:
      line = line.strip()
      if line.startswith('c'):
        continue
      if line.startswith('p cnf'):
        parts = line.split()
        num_variables = int(parts[2])
        num_clauses = int(parts[3])
        check = True
        continue
      if check == True:
        clause = line.split()
        for i in range(len(clause)):
          clause[i] = int(clause[i])
        clauses_dict[f"c{clauses_count}"]=clause
        clauses_count += 1
    return clauses_dict, num_variables, num_clauses
# clauses는 clause [3, 39, -58, 0] 이런 식으로 저장되어 있음

class clause_struct:
  def __init__(self, clauses_dict, result):
    self.clause = clauses_dict # {c1 : -1 2 0, c2 : -3 4 5 0, ... ,} 이런 식의 저장
    self.result = result # Boolean
class Variables_struct:
  def __init__(self, value, decision_level, reason):
    self.value = value # 변수가 저장될 bool 타입 변수이면 -> small int 형 (1 = True, -1 = False) -> 어차피 clause가 -로 받아서 곱해서 판단하는게 연산량이 더 적다고 생각
    self.decision_level = decision_level
    self.reason = reason # 어느 절의 영향을 받아 결정된 변수인지를 의미 (나중에 추적하기 위함) / default는 None이며 None이라면 절의 영향을 받은 것이 아닌 할당 받은 값
class SATSolver:
  def __init__(self, variables, clauses):
    self.variables = {}
    self.result_clause = {} # clause의 unit clause 판단을 위한 부분 / 시간 단축을 위하여 공간을 더 사용
    self.num_variables = variables # 변수의 개수를 index 크기로 구현
    self.clauses_json = clauses    # -1 2 0 등을 저장 not x1 or x2 이런 식을 의미
    self.learning_clauses = []     # 에러가 났을 경우 배우는 절
    self.level = 1                 # Decision level 체크 용
    self.variable_flag = [False]*(variables+1)# 변수의 실제 값 할당의 경우 할당한 적 없는 변수만을 할당해야 하기 때문에 변수의 할당 여부 체크 용
    self.clauses_key = []
    self.clauses = []
    self.tried = {}
    self.unsat_detected = False

  def backtrack(self, target_level):
      """target_level보다 높은 레벨의 할당을 모두 취소"""
      vars_to_remove = []
      for var_idx, var_info in self.variables.items():
          if var_info.decision_level > target_level:
              vars_to_remove.append(var_idx)

      for var_idx in vars_to_remove:
          del self.variables[var_idx]
          self.variable_flag[var_idx] = False
          # ✅ 해당 변수의 tried 초기화
          if var_idx in self.tried:
              del self.tried[var_idx]

      for clause_key in self.result_clause:
          self.result_clause[clause_key].result = False

      self.level = target_level

      decision_var = None
      for var_idx, var_info in self.variables.items():
          if var_info.decision_level == target_level and var_info.reason is None:
              decision_var = var_idx
              break

      if decision_var is None:
          if target_level > 1:
              self.backtrack(target_level - 1)
          else:
              self.unsat_detected = True
          return

      current_val = self.variables[decision_var].value

      if decision_var not in self.tried:
          self.tried[decision_var] = set()

      self.tried[decision_var].add(current_val)

      if len(self.tried[decision_var]) >= 2:
          del self.variables[decision_var]
          self.variable_flag[decision_var] = False
          del self.tried[decision_var]

          if target_level > 1:
              self.backtrack(target_level - 1)
          else:
              self.unsat_detected = True
      else:
          self.variables[decision_var].value *= -1
  def solve(self):
      for clause_key, clause_value in self.clauses_json.items():
          self.clauses_key.append(clause_key)
          self.result_clause[clause_key] = clause_struct(clause_value, False)
          self.clauses.append(clause_value)
      start_time = time.time()
      iteration = 0
      while (True):
          iteration += 1
          if time.time() - start_time > 9:
              print("UNSAT")
              return False
          # ✅ 매 100번마다 출력 (1000 → 100)
          if iteration % 5000 == 0:
              print(f"Iter: {iteration}, Level: {self.level}, Assigned: {len(self.variables)}/{self.num_variables}")

          total_result = True
          for clause in self.result_clause.values():
              if clause.result is False:
                  total_result = False
                  break
          if total_result == True:
              print("SAT")
              result_assignment = []
              for i in range(1, self.num_variables + 1):
                  if i in self.variables:
                      result_assignment.append(i * self.variables[i].value)
                  else:
                      result_assignment.append(i)
              print(" ".join(map(str, result_assignment)))
              break

          change_check = True
          conflict_occurred = False

          while change_check:

              change_check = False
              for clause_key, clause in zip(self.clauses_key, self.clauses):
                  unassigned_variable = []
                  for clause_idx in clause:
                      if clause_idx == 0:
                          if len(unassigned_variable) == 1 and self.result_clause[clause_key].result == False:
                              if unassigned_variable[0] < 0:
                                  self.variables[abs(unassigned_variable[0])] = Variables_struct(-1,
                                                                                                 decision_level=self.level,
                                                                                                 reason=clause_key)
                              else:
                                  self.variables[abs(unassigned_variable[0])] = Variables_struct(1,
                                                                                                 decision_level=self.level,
                                                                                                 reason=clause_key)
                              change_check = True
                              self.variable_flag[abs(unassigned_variable[0])] = True
                          elif len(unassigned_variable) == 0 and self.result_clause[clause_key].result == False:
                              if self.level == 1:
                                  print("UNSAT")
                                  return False
                              else:
                                  self.backtrack(self.level - 1)
                                  if self.unsat_detected:
                                      print("UNSAT")
                                      return False
                                  change_check = True
                                  conflict_occurred = True
                          break

                      if abs(clause_idx) in self.variables:
                          if self.variables[abs(clause_idx)].value * clause_idx > 0:
                              self.result_clause[clause_key].result = True
                          else:
                              pass
                      else:
                          unassigned_variable.append(clause_idx)

              if conflict_occurred:
                  break

          if not conflict_occurred and not change_check:
              next_var = None
              for i in range(1, self.num_variables + 1):
                  if not self.variable_flag[i]:
                      next_var = i
                      break

              if next_var is None:
                  break

              self.level += 1
              self.variables[next_var] = Variables_struct(1, decision_level=self.level, reason=None)
              self.variable_flag[next_var] = True


import sys
import os
import time

# ... (기존 get_file, clause_struct, Variables_struct, SATSolver 코드)

if __name__ == "__main__":
  # 테스트 폴더 경로
  test_folder = r"C:\Users\김용민\PycharmProjects\pythonProject\hw2_testcases\unsat"

  # 결과 저장
  results = []

  # problem_001.cnf부터 problem_050.cnf까지
  for i in range(1, 51):
    filename = f"problem_{i:03d}.cnf"  # problem_001, problem_002, ...
    filepath = os.path.join(test_folder, filename)

    if not os.path.exists(filepath):
      print(f"❌ {filename} not found")
      continue

    print(f"\n{'=' * 50}")
    print(f"Testing: {filename}")
    print(f"{'=' * 50}")

    try:
      # 시간 측정 시작
      start_time = time.time()

      # 파일 파싱
      clauses_dict, num_variables, num_clauses = get_file(filepath)
      print(f"Variables: {num_variables}, Clauses: {num_clauses}")

      # SAT Solver 실행
      solver = SATSolver(num_variables, clauses_dict)
      result = solver.solve()

      # 시간 측정 종료
      elapsed_time = time.time() - start_time

      # 결과 저장
      results.append({
        'file': filename,
        'variables': num_variables,
        'clauses': num_clauses,
        'time': elapsed_time,
        'result': 'SAT' if result != False else 'UNSAT'
      })

      print(f"✅ Time: {elapsed_time:.3f}s")

    except Exception as e:
      print(f"❌ Error: {e}")
      results.append({
        'file': filename,
        'error': str(e)
      })

  # 최종 결과 출력
  print(f"\n{'=' * 70}")
  print("SUMMARY")
  print(f"{'=' * 70}")
  print(f"{'File':<20} {'Variables':<12} {'Clauses':<10} {'Time (s)':<12} {'Result'}")
  print(f"{'-' * 70}")

  for r in results:
    if 'error' in r:
      print(f"{r['file']:<20} ERROR: {r['error']}")
    else:
      print(f"{r['file']:<20} {r['variables']:<12} {r['clauses']:<10} {r['time']:<12.3f} {r['result']}")

  # 통계
  success_count = sum(1 for r in results if 'error' not in r)
  total_time = sum(r['time'] for r in results if 'time' in r)
  avg_time = total_time / success_count if success_count > 0 else 0

  print(f"\n{'=' * 70}")
  print(f"Total: {len(results)} files")
  print(f"Success: {success_count} files")
  print(f"Total Time: {total_time:.3f}s")
  print(f"Average Time: {avg_time:.3f}s")
  print(f"{'=' * 70}")