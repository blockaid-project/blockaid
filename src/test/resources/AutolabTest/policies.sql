SELECT users.* FROM users WHERE users.id = _MY_UID;

SELECT course_user_data.* FROM course_user_data WHERE course_user_data.user_id = _MY_UID;
-- SELECT o.* FROM course_user_data o, course_user_data me WHERE me.user_id = _MY_UID AND me.course_assistant = true AND o.course_id = me.course_id AND o.section = me.section;
-- Autolab seems to allow a course assistant to grade any student's assessment.
-- SELECT o.* FROM course_user_data o, course_user_data me WHERE me.user_id = _MY_UID AND me.course_assistant = true AND o.course_id = me.course_id;
SELECT o.* FROM course_user_data o, course_user_data me WHERE me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true) AND o.course_id = me.course_id;
SELECT users.id, users.first_name, users.last_name, users.email, users.school, users.major, users.`year`, users.administrator FROM users, course_user_data o, course_user_data me WHERE me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true) AND o.course_id = me.course_id AND users.id = o.user_id;

-- Autolab reveals the distinction between a class being nonexistent (404) and
-- a user not being enrolled in an class that does exist
-- ("User john_doe@example.com is not in this course").  Strictly speaking, the
-- `id` column doesn't have to be revealed, but it doesn't contain any sensitive
-- information (`id` and `name` are a one-to-one correspondence) so we leave it in.
SELECT courses.id, courses.name FROM courses;
-- An enrolled student can see whether the course's display name and semester (shown on front page), start and end dates (not sensitive), and whether it is disabled or not...
-- The rest of the fields don't seem sensitive anyway, so let's reveal all fields of the `courses` table regardless of `disabled`.
-- (Of course, the visibility of associated course resources, like assignments, still depends on whether the course is disabled.)
SELECT courses.* FROM courses, course_user_data WHERE courses.id = course_user_data.course_id AND course_user_data.user_id = _MY_UID;

SELECT announcements.* FROM announcements WHERE announcements.`system` = true;
-- TODO(zhangwen): Autolab has two issues surrounding announcements:
--    1. Persistent announcements seem to be displayed regardless of the start & end date times.
--    2. On the announcement view frontend I can't pick the start & end date times properly.
--  Thus, these policies here allow access to announcements regardless of start & end times.
-- SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = false AND announcements.start_date < _NOW AND announcements.end_date > _NOW;
SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = false;
SELECT announcements.* FROM announcements, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = announcements.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true;

-- These fields are visible whether or not the assessment is released, and whether or not the course is disabled---
-- * A list of assessments for disabled courses show up on the front page.
-- * The date-related fields are used for grace-day calculation, which involves all assignments.
SELECT assessments.id, assessments.course_id, assessments.name, assessments.display_name, assessments.start_at, assessments.end_at, assessments.due_at, assessments.max_grace_days, assessments.category_name, assessments.updated_at FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID;
-- But other fields are only visible for released assignments, i.e., those with `start_at < _NOW`.
SELECT assessments.* FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = false;
SELECT assessments.* FROM assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.course_assistant = true AND courses.disabled = false;
SELECT assessments.* FROM assessments, course_user_data WHERE assessments.course_id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true;

-- We allow viewing assessment user data regardless of whether the assessment is released or not
-- because it doesn't include sensitive information about the course.
SELECT assessment_user_data.* FROM assessment_user_data, course_user_data WHERE assessment_user_data.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;
-- SELECT assessment_user_data.* FROM assessment_user_data, course_user_data o, course_user_data me WHERE assessment_user_data.course_user_datum_id = o.id AND o.course_id = me.course_id AND o.section = me.section AND me.user_id = _MY_UID AND me.course_assistant = true;
-- SELECT assessment_user_data.* FROM assessment_user_data, course_user_data o, course_user_data me WHERE assessment_user_data.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND me.course_assistant = true;
SELECT assessment_user_data.* FROM assessment_user_data, course_user_data o, course_user_data me WHERE assessment_user_data.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true);

SELECT `groups`.* FROM `groups`, assessment_user_data, course_user_data WHERE `groups`.id = assessment_user_data.group_id AND assessment_user_data.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;
SELECT `groups`.* FROM `groups`, assessment_user_data, course_user_data o, course_user_data me WHERE `groups`.id = assessment_user_data.group_id AND assessment_user_data.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND me.instructor = true;

-- TODO(zhangwen): The application seems fine with showing unreleased attachments.  I filed an issue on GitHub.
-- TODO(zhangwen): The application also seems fine with showing attachments of assessments that haven't started...
-- SELECT attachments.* FROM attachments, courses, course_user_data WHERE attachments.released = true AND courses.id = course_user_data.course_id AND courses.id = attachments.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = false;
SELECT attachments.* FROM attachments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = attachments.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = false;

-- Within an accessible course, Autolab allows the user to distinguish between a nonexistent submission ID vs an
-- existing one that the user has no access to.
SELECT courses.id, assessments.id, submissions.id FROM submissions, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = false AND submissions.assessment_id = assessments.id;
-- Every field other than real_filename.
-- These are my own submissions.  I should be allowed to see them even if the assessment hasn't started... (this could happen if the assessment start date is pushed to the future after my submission).
SELECT `submissions`.`id`, `submissions`.`version`, `submissions`.`course_user_datum_id`, `submissions`.`assessment_id`, `submissions`.`filename`, `submissions`.`created_at`, `submissions`.`updated_at`, `submissions`.`notes`, `submissions`.`mime_type`, `submissions`.`special_type`, `submissions`.`submitted_by_id`, `submissions`.`autoresult`, `submissions`.`detected_mime_type`, `submissions`.`submitter_ip`, `submissions`.`tweak_id`, `submissions`.`ignored`, `submissions`.`dave`, `submissions`.`settings`, `submissions`.`embedded_quiz_form_answer`, `submissions`.`submitted_by_app_id` FROM submissions, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND courses.disabled = false AND submissions.assessment_id = assessments.id AND submissions.course_user_datum_id = course_user_data.id;
-- File name is only visible in none-exam settings.
SELECT submissions.* FROM submissions, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.exam = false AND courses.disabled = false AND courses.exam_in_progress = false AND submissions.assessment_id = assessments.id AND submissions.course_user_datum_id = course_user_data.id;
SELECT submissions.* FROM submissions, course_user_data o, course_user_data me WHERE submissions.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true);

SELECT annotations.* FROM annotations, submissions, assessments, courses, course_user_data WHERE annotations.submission_id = submissions.id AND courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND _NOW < assessments.grading_deadline AND assessments.exam = false AND courses.disabled = false AND courses.exam_in_progress = false AND submissions.assessment_id = assessments.id AND submissions.course_user_datum_id = course_user_data.id;
SELECT annotations.* FROM annotations, submissions, course_user_data o, course_user_data me WHERE annotations.submission_id = submissions.id AND submissions.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true);

SELECT scores.* FROM scores, submissions, course_user_data WHERE scores.submission_id = submissions.id AND scores.released = true AND submissions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;
-- SELECT scores.* FROM scores, submissions, course_user_data o, course_user_data me WHERE scores.submission_id = submissions.id AND submissions.course_user_datum_id = o.id AND o.course_id = me.course_id AND o.section = me.section AND me.user_id = _MY_UID AND me.course_assistant = true;
-- SELECT scores.* FROM scores, submissions, course_user_data o, course_user_data me WHERE scores.submission_id = submissions.id AND submissions.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND me.course_assistant = true;
SELECT scores.* FROM scores, submissions, course_user_data o, course_user_data me WHERE scores.submission_id = submissions.id AND submissions.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true);

SELECT extensions.* FROM extensions, course_user_data WHERE extensions.course_user_datum_id = course_user_data.id AND course_user_data.user_id = _MY_UID;
SELECT extensions.* FROM extensions, course_user_data o, course_user_data me WHERE extensions.course_user_datum_id = o.id AND o.course_id = me.course_id AND me.user_id = _MY_UID AND (me.instructor = true OR me.course_assistant = true);

SELECT scoreboards.* FROM scoreboards, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = false AND scoreboards.assessment_id = assessments.id;
SELECT scoreboards.* FROM scoreboards, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.course_assistant = true AND courses.disabled = false AND scoreboards.assessment_id = assessments.id;
SELECT scoreboards.* FROM scoreboards, assessments, course_user_data WHERE assessments.course_id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true AND scoreboards.assessment_id = assessments.id;

SELECT problems.* FROM problems, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND assessments.start_at < _NOW AND courses.disabled = false AND problems.assessment_id = assessments.id;
SELECT problems.* FROM problems, assessments, courses, course_user_data WHERE courses.id = course_user_data.course_id AND courses.id = assessments.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.course_assistant = true AND courses.disabled = false AND problems.assessment_id = assessments.id;
SELECT problems.* FROM problems, assessments, course_user_data WHERE assessments.course_id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true AND problems.assessment_id = assessments.id;

-- doesn't seem to include sensitive information.
SELECT score_adjustments.* FROM score_adjustments;

-- From `app/controllers/schedulers_controller.rb`:
--   Tasks don't actually get accurately scheduled, but with each request, we check all schedulers, and if one hasn't
--   ran in more than its period's time, it's function is run.
-- Thus, every page load checks for _any_ tasks ready to run; this necessitates a policy that allows reading rows from
-- the `scheduler` table irrespective of `course_id`.  This is unideal, but can't be rectified without extensive
-- application change.
SELECT scheduler.* FROM scheduler;

SELECT schema_migrations.* FROM schema_migrations;

SELECT risk_conditions.* FROM risk_conditions, course_user_data WHERE risk_conditions.course_id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true;
SELECT watchlist_instances.* FROM watchlist_instances, course_user_data WHERE watchlist_instances.course_id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true;
SELECT autograders.* FROM autograders, assessments, course_user_data WHERE autograders.assessment_id = assessments.id AND assessments.course_id = course_user_data.course_id AND course_user_data.user_id = _MY_UID AND course_user_data.instructor = true;

SELECT o.* FROM users o, users me WHERE me.id = _MY_UID AND me.administrator = true;
SELECT course_user_data.* FROM course_user_data, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT courses.* FROM courses, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT announcements.* FROM announcements, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT assessments.* FROM assessments, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT assessment_user_data.* FROM assessment_user_data, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT `groups`.* FROM `groups`, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT attachments.* FROM attachments, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT submissions.* FROM submissions, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT annotations.* FROM annotations, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT scores.* FROM scores, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT extensions.* FROM extensions, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT scoreboards.* FROM scoreboards, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT problems.* FROM problems, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT risk_conditions.* FROM risk_conditions, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT watchlist_instances.* FROM watchlist_instances, users WHERE users.id = _MY_UID AND users.administrator = true;
SELECT autograders.* FROM autograders, users WHERE users.id = _MY_UID AND users.administrator = true;
