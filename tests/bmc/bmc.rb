n = 100

def vars_in_row(row, n)
  str = ""
  n.times { |i| str += "#{n*row + i + 1} " }
  str
end

def vars_in_col(col, n)
  str = ""
  n.times { |i| str += "#{n*i + col + 1} " }
  str
end


(1..32).each do |k_1|
  k_2 = k_1 + 5

  File.open("bmc_100_#{k_1}_#{k_2}.cnfp", 'w') do |file|
    file << "c Booblean Matrix Cardinality instance with n=#{n}, k_1=#{k_1}, k_2=#{k_2}\n"
    file << "p cnf+ #{n*n} #{4*n}\n"

    n.times do |row|
      file << vars_in_row(row, n) + "<= #{k_2}\n"
      file << vars_in_row(row, n) + ">= #{k_1}\n"
    end

    n.times do |col|
      file << vars_in_col(col, n) + "<= #{k_2}\n"
      file << vars_in_col(col, n) + ">= #{k_1}\n"
    end
  end
end
