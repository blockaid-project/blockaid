-- SELECT `assessments`.`id`, `assessments`.`course_id` FROM `assessments`, `assessment_user_data`, `course_user_data` WHERE `assessment_user_data`.`course_user_datum_id` = `course_user_data`.`id` AND `assessment_user_data`.`assessment_id` = `assessments`.`id`; SELECT `assessments`.`id`, `course_user_data`.`course_id` FROM `assessments`, `assessment_user_data`, `course_user_data` WHERE `assessment_user_data`.`course_user_datum_id` = `course_user_data`.`id` AND `assessment_user_data`.`assessment_id` = `assessments`.`id`;
