#!/usr/bin/env python3
"""Finite, exact checks of the integral tensor constructions.

These checks use integer coordinates and coefficients only.  They verify the
specified finite ranges; the accompanying formulas provide the general proofs.
Run with: python3 verify_integral_constructions.py
"""

from collections import Counter


def bareiss_determinant(matrix):
    """Compute a determinant using exact integer elimination."""
    data = [row[:] for row in matrix]
    size = len(data)
    sign = 1
    previous = 1
    for column in range(size - 1):
        pivot_row = next(
            (row for row in range(column, size) if data[row][column]), None
        )
        if pivot_row is None:
            return 0
        if pivot_row != column:
            data[column], data[pivot_row] = data[pivot_row], data[column]
            sign = -sign
        pivot = data[column][column]
        for row in range(column + 1, size):
            for other in range(column + 1, size):
                numerator = (
                    pivot * data[row][other]
                    - data[row][column] * data[column][other]
                )
                assert numerator % previous == 0
                data[row][other] = numerator // previous
            data[row][column] = 0
        previous = pivot
    return sign * data[-1][-1]


def check_separator():
    source_terms = 0
    retained_terms = 0
    zero_terms = 0
    for size in range(1, 11):
        transformed = Counter()
        length = 2 * size - 1
        # Each original matched sector has its own Y and Z coordinates.
        for sector in range(1, size + 1):
            for first in range(length):
                for second in range(length):
                    source_terms += 1
                    output = first + second
                    assert 0 <= output < 4 * size - 3
                    if first % 2:
                        continue
                    tentative = first // 2 + 1
                    dot_y = second + sector - size + 1
                    dot_z = output - sector - size + 3
                    if not (1 <= dot_y <= size and 1 <= dot_z <= size):
                        continue
                    transformed[tentative, sector, dot_y, dot_z] += 1
        expected = Counter(
            (tentative, sector, dot_y, dot_z)
            for tentative in range(1, size + 1)
            for sector in range(1, size + 1)
            for dot_y in range(1, size + 1)
            for dot_z in range(1, size + 1)
            if dot_y - dot_z + 2 * (tentative - sector) == 0
        )
        assert transformed == expected
        zero = Counter()
        for (tentative, sector, dot_y, dot_z), coefficient in transformed.items():
            first = 2 * tentative - 2
            second = dot_y - sector + size - 1
            output = dot_z + sector + size - 3
            assert 0 <= first < length
            assert 0 <= second < length
            assert 0 <= output < 4 * size - 3
            assert first + second == output
            weight = tentative**2 + sector * dot_y - sector**2 - sector * dot_z
            assert weight == (tentative - sector) ** 2 >= 0
            retained_terms += coefficient
            if weight == 0:
                zero[tentative, sector, dot_y, dot_z] += coefficient
        desired = Counter(
            (sector, sector, dot, dot)
            for sector in range(1, size + 1)
            for dot in range(1, size + 1)
        )
        assert zero == desired
        zero_terms += sum(zero.values())
    return 10, source_terms, retained_terms, zero_terms


def check_tripling():
    source_terms = 0
    zero_terms = 0
    discarded_terms = 0
    for first_length in range(1, 9):
        for short_length in range(1, 9):
            long_length = 3 * short_length + first_length - 1
            right_start = 2 * short_length + first_length - 1

            def y_sector(index):
                if index < short_length:
                    return 0
                if index < right_start:
                    return 1
                return 2

            def z_sector(index):
                if index < short_length + first_length - 1:
                    return 0
                if index < right_start:
                    return 1
                return 2

            zero = Counter()
            for first in range(first_length):
                for second in range(long_length):
                    source_terms += 1
                    output = first + second
                    y_label = y_sector(second)
                    z_label = z_sector(output)
                    weight = int(y_label == 1) - int(z_label == 1)
                    assert weight >= 0
                    assert (weight == 0) == (y_label == z_label)
                    if weight == 0:
                        zero[first, second, output] += 1
                    else:
                        discarded_terms += 1
            left = Counter(
                (first, second, first + second)
                for first in range(first_length)
                for second in range(short_length)
            )
            right = Counter(
                (first, right_start + second, right_start + first + second)
                for first in range(first_length)
                for second in range(short_length)
            )
            middle = Counter(
                (
                    first_length - 1 - reverse,
                    short_length + reverse + other_input,
                    short_length + first_length - 1 + other_input,
                )
                for reverse in range(first_length)
                for other_input in range(short_length)
            )
            assert zero == left + middle + right
            assert not (left.keys() & middle.keys())
            assert not (left.keys() & right.keys())
            assert not (middle.keys() & right.keys())
            for first, second, output in middle:
                reverse = first_length - 1 - first
                other_input = output - (short_length + first_length - 1)
                product_output = second - short_length
                assert y_sector(second) == z_sector(output) == 1
                assert product_output == reverse + other_input
                assert 0 <= reverse < first_length
                assert 0 <= other_input < short_length
            zero_terms += sum(zero.values())
    return 64, source_terms, zero_terms, discarded_terms


def determinant_basis(degree):
    # Ambient rows: A_0,...,A_e,B_0,...,B_e.
    # New columns: A_0,...,A_e,B_e,K_0,...,K_{e-1},
    # where K_j = B_j - A_{j+1} = (uw-vs)u^{e-1-j}v^j.
    size = 2 * (degree + 1)
    columns = []
    for index in range(degree + 1):
        column = [0] * size
        column[index] = 1
        columns.append(column)
    column = [0] * size
    column[-1] = 1
    columns.append(column)
    for index in range(degree):
        column = [0] * size
        column[degree + 1 + index] = 1
        column[index + 1] = -1
        columns.append(column)
    return [[columns[column][row] for column in range(size)] for row in range(size)]


def to_filtration_coordinates(ambient, degree):
    quotient = ambient[: degree + 1] + [ambient[-1]]
    kernel = ambient[degree + 1 : -1]
    # Explicit integral inverse: B_j = K_j + A_{j+1} (j < e).
    for index, coefficient in enumerate(kernel):
        quotient[index + 1] += coefficient
    return quotient, kernel


def multiply_ambient(ambient, input_degree, multiplier_v_degree, multiplier_degree):
    output_degree = input_degree + multiplier_degree
    output = [0] * (2 * (output_degree + 1))
    for index in range(input_degree + 1):
        output[index + multiplier_v_degree] += ambient[index]
        output[output_degree + 1 + index + multiplier_v_degree] += (
            ambient[input_degree + 1 + index]
        )
    return output


def check_determinant_filtration():
    determinants = []
    inverse_vectors = 0
    for degree in range(1, 11):
        basis = determinant_basis(degree)
        determinant = bareiss_determinant(basis)
        assert abs(determinant) == 1
        determinants.append(determinant)
        for ambient_index in range(2 * (degree + 1)):
            ambient = [0] * (2 * (degree + 1))
            ambient[ambient_index] = 1
            quotient, kernel = to_filtration_coordinates(ambient, degree)
            coordinates = quotient + kernel
            reconstructed = [
                sum(coefficient * value for coefficient, value in zip(row, coordinates))
                for row in basis
            ]
            assert reconstructed == ambient
            inverse_vectors += 1

    slices = 0
    quotient_columns = 0
    kernel_columns = 0
    for first_length in range(1, 9):
        for second_length in range(2, 9):
            input_degree = second_length - 1
            output_degree = first_length + second_length - 2
            input_basis = determinant_basis(input_degree)
            for multiplier_index in range(first_length):
                slices += 1
                for column_index in range(2 * second_length):
                    ambient = [row[column_index] for row in input_basis]
                    multiplied = multiply_ambient(
                        ambient, input_degree, multiplier_index, first_length - 1
                    )
                    quotient, kernel = to_filtration_coordinates(multiplied, output_degree)
                    if column_index < second_length + 1:
                        # Quotient basis has degree b; multiply by degree a-1.
                        expected = [0] * (output_degree + 2)
                        expected[column_index + multiplier_index] = 1
                        assert quotient == expected
                        quotient_columns += 1
                    else:
                        # D times a degree b-2 monomial stays divisible by D.
                        kernel_index = column_index - (second_length + 1)
                        assert quotient == [0] * (output_degree + 2)
                        expected = [0] * output_degree
                        expected[kernel_index + multiplier_index] = 1
                        assert kernel == expected
                        kernel_columns += 1
    return determinants, inverse_vectors, slices, quotient_columns, kernel_columns


def main():
    separator = check_separator()
    tripling = check_tripling()
    determinants, inverse_vectors, slices, quotient_columns, kernel_columns = (
        check_determinant_filtration()
    )
    print(
        "separator: %d sizes; %d source terms; %d terms after restriction; "
        "%d zero-weight terms" % separator
    )
    print(
        "tripling: %d shapes; %d source terms; %d zero-weight terms; "
        "%d discarded terms" % tripling
    )
    print(
        "determinant basis: 10 degrees; determinants=%s; "
        "%d ambient vectors checked against the integral inverse"
        % (determinants, inverse_vectors)
    )
    print(
        "multiplication compatibility: 56 shapes; %d monomial slices; "
        "%d quotient columns; %d kernel columns" % (slices, quotient_columns, kernel_columns)
    )
    print("All exact integer checks passed.")


if __name__ == "__main__":
    main()
